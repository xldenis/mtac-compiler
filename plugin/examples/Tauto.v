Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Require Import MtacLite.MtacLite.

Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.

Definition simple_tauto :=
  mfix f (p : Prop) : M p :=
    eq <- unify True p;

    match eq with
    | Some prf => @eq_rect Prop True (Mtac) (ret I) p prf
    | Nothing =>
      x <- evar;
      y <- evar;

      eq <- unify (x /\ y) p;
      match eq with
      | Some prf =>
        pX <- f x;
        pY <- f y;

        @eq_rect Prop _ Mtac (ret (conj pX pY)) p prf
      | Nothing =>
        x <- evar;
        y <- evar;

        eq <- unify (x \/ y) p;

        match eq with
        | Some prf =>
          try (
            r1 <- f x;

            @eq_rect Prop (x \/ y) Mtac (ret (@or_introl x y r1)) p prf
          ) (
            r2 <- f y;

            @eq_rect Prop (x \/ y) Mtac (ret (@or_intror x y r2)) p prf
          )
         | Nothing => fail "Not Found"
        end
      end
    end
  .

Check simple_tauto.

Definition simple_fix :=
  mfix f (p : nat) : M True :=
    match p with
    | 0 => ret I
    | n => f (n - 1) ;; f (n - 1)
    end
  .


Example fix_ex : True.
Proof.
  compile (simple_fix 2) as v.
  exact v.
Qed.

(*   run (is_or (True \/ (True \/ False))). *)
(* Qed. *)

Example ex0 : True \/ False.
Proof.
  run (simple_tauto (True \/ False)).
  all: (exact True).
Qed.

Example ex1 : True.
  run (simple_tauto True) as v.
  exact v.
Qed.
Example ex2 : True /\ True.
Proof.
  compile (simple_tauto (True /\ True)) as v.
  exact v.
  Unshelve.
  all: exact True.
Qed.

Example ex3 : True /\ (False \/ True).
Proof.
  compile (simple_tauto (True /\ (False \/ True))) as v.
  exact v.
  Unshelve.
  all: (exact True).
Qed.

