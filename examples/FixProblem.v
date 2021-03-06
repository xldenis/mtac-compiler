Require Import String.

Inductive Mtac : Type -> Prop :=
  | print : string -> Mtac unit
  | ret   : forall {A}, A -> Mtac A
  | bind  : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B
  | unify : forall {A} (x y : A) ,Mtac ({ x = y } + {x <> y })
  | fix'  : forall {A B} (S : Type -> Prop),
    (forall a, S a -> Mtac a) ->
    ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
    forall x : A, Mtac (B x)
  | fail : forall {A}, string -> Mtac A
  | nu : forall {A B}, (A -> Mtac B) -> Mtac B (*idk if we actually need nu*)
  | evar : forall {A}, Mtac A
  | try : forall {A}, Mtac A -> Mtac A -> Mtac A
  .

Notation "'mfix' f ( x : A ) : 'M' T := b" :=
  (@fix' A (fun x => T) Mtac (fun a (x : Mtac a) => x) (fun f x => b))
  (at level 85, f at level 0, x at next level, format
  "'[v  ' 'mfix'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Definition simpl_prop_auto :=
(*
  @fix' Prop (fun p => p) Mtac (fun a (x : Mtac a) => x) (fun f p => fail "omg").


*)
  mfix f (p : Prop) : M p := (* problem is here*)
    fail "omg"
  .
Check simpl_prop_auto.
