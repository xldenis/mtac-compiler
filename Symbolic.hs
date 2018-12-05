#!/usr/bin/env stack
-- stack --resolver lts-12.0 --install-ghc runghc --package bound --package prettyprinter
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module SymbolicCalc where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

import Data.Text.Prettyprint.Doc
import Bound

-- Fresh names

class Monad m => MonadFresh m where
  fresh :: m Int

type Fresh a = FreshT Identity a

evalFresh :: Int -> Fresh a -> a
evalFresh i = runIdentity . flip evalStateT i . unFreshT

newtype FreshT m a = FreshT { unFreshT :: StateT Int m a }
  deriving (Functor, Applicative, Monad, MonadState Int)

instance Monad m => MonadFresh (FreshT m) where
  fresh = do
    next <- get
    modify (+ 1)
    return next

prefixed :: MonadFresh m => String -> m String
prefixed pre = (pre ++) . show <$> fresh

-- Symbolic Calculus
data Term y x
  = Var x
  | App (Term y x) (Term y x)
  | Lam (Scope () (Term y) x)
  | Acc y [Term y x]
  deriving (Functor)

infixl 9 .@

(.@) :: (Term y x) -> (Term y x) -> (Term y x)
(.@) = App

instance Applicative (Term y) where
  pure = Var
  (<*>) = ap

instance Monad (Term y) where
  return = pure

  (Var a) >>= f = f a
  (App l r) >>= f = App (l >>= f) (r >>= f)
  (Lam x) >>= f = Lam (x >>>= f)
  (Acc fr ts) >>= f = Acc fr (map (>>= f) ts)

-- -- Reduction Rules

weaksymred :: Term y x -> Term y x
weaksymred (App f r) = let
  r' = weaksymred r
  in case weaksymred f of
    (Lam t) -> weaksymred (instantiate1 r' t)
    (Acc fr ts) -> Acc fr (ts ++ [r'])
    e -> App e r'
weaksymred x = x

-- Builder

lam v b = Lam (abstract1 v b)

free x = Acc x []

readback :: ( MonadFresh m) => Term Char Char -> m (Doc ann)
readback (Lam t) = do
  v <- toEnum <$> fresh
  body <- n (instantiate1 (Var v) t)
  return $ pretty "\\" <> pretty (v :: Char) <+> pretty "->" <+> body
  where n = readback . weaksymred
readback (Var x) = return $ pretty x
readback (Acc f ts) = do
  ts' <- mapM readback ts

  return $ pretty f <> brackets (hcat ts')
readback (App l r) = do
  l' <- readback l
  r' <- readback r

  return $ l' <+> r'

pprint :: (MonadFresh m) => Term Char Char -> m (Doc ann)
pprint (Lam t) = do
  v <- toEnum <$> fresh
  b <- pprint (instantiate1 (Var v) t)
  return $ pretty "\\" <> pretty (v :: Char) <+> pretty "->" <+> b
pprint (Var x) = return $ pretty x
pprint (Acc f ts) = do
  ts' <- mapM pprint ts

  return $ pretty f <> brackets (hcat ts')
pprint (App l r) = do
  l' <- pprint l
  r' <- pprint r

  return $ (if isVar l then l' else parens l') <+> (if isVar r then r' else parens r')
  where
  isVar (Var _) = True
  isVar (Acc _ _) = True
  isVar _ = False

simpl :: Term Char Char
simpl = lam 'X' $ lam 'Y' $ Var 'X' .@ Var 'Y'

freeV = lam 'X' $ free 'A' .@ Var 'X'

norm = (lam 'X' (Var 'X' .@ (lam 'X' (Var 'X')))) .@ (free 'A')

normalize = evalFresh 97 . readback . weaksymred

showFunc f = do
  print $ pretty "func:" <+> evalFresh 97 (pprint f)
  print $ pretty "norm:" <+> normalize f

main = do
  showFunc simpl
  showFunc freeV
  showFunc norm
