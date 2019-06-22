Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Add LoadPath "../examples".
Require Import List.

Import ListNotations.
Require Import MtacLite.MtacLite.
Import MtacLite.MtacLiteNotations.
Import Coq.Strings.String.

Delimit Scope M_scope with M.

Definition search {A} (x : A) :=
  mfix f (s : list A) : M (In x s) :=
  (mmatch s as s' return M (In x s') with
  | [? s'] (x :: s') => ret (in_eq _ _)
  | [? y s'] (y :: s') =>
      r <- f s';
      ret (in_cons _ _ _ r)
  | [? x] x => fail "Not Found"
  end)%M.

Definition search' {A} (x : A) :=
  mfix f (s : list A) : M (In x s) :=

  s' <- evar;
  y  <- evar;

  eq <- unify (x :: s') s;

  match eq with
  | Some prf =>
    @eq_rect _ _ Mtac (ret (in_eq x s')) (In x s) (f_equal _ prf)
  | None =>
      eq <- unify (y :: s') s;
      match eq with
      | Some prf => r <- f s';

        @eq_rect _ _ Mtac (ret (in_cons _ _ _ r)) (In x s) (f_equal _ prf)
      | _ => fail "Not Found"
      end
  end.


Definition search'' {A} (x : A) :=
  mfix f (s : list A) : M (True) :=

  s' <- evar;
  y  <- evar;

  eq <- unify (x :: s') s;

  match eq with
  | Some prf => ret I
  | None =>
      eq <- unify (y :: s') s;
      match eq with
      | Some prf => f s'
      | _ => fail "Not Found"
      end
  end.

Lemma z_in_xyz {A} (x y z : A) : In z [x; y; z].
Proof.
  run (search z [x; y; z]).
Qed.

Fixpoint replicate {A} (t : nat) (x : A) : list A :=
  match t with
  | 0 => nil
  | S n => x :: replicate n x
  (* | _ => let xs := replicate x (t - 1) in (x :: xs) *)
  end.

Lemma bench : True.
 pose (replicate 1000 False ++ [True]).
 (*compute in  l.*)
 Time run (search'' True (l)) as v.
 Time compile (search'' True ((replicate 1000 False ++ [True]))) as v2.


