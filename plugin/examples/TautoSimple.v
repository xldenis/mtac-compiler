Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Add LoadPath ".".

Require Import MtacLite.MtacLite.
Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.
Require Import List.

Record dyn := Dyn { prop : Prop ; elem : prop }.

Definition search (P : Prop) :=
  mfix f (s:list dyn) : M P :=
    match s with
    | Dyn A x :: s' =>
      eq <- unify A P;
        match eq with
        | Some prf => @eq_rect Prop _ Mtac (ret x) P prf
        | Nothing => f s'
        end
    | nil => fail "empty"
    end.

Definition simple_tauto (j : Prop) :=
  mfix2 f (p : Prop) (hyps : list dyn) : M p :=
    eq <- unify True p;

    match eq with
    | Some prf => @eq_rect Prop True (Mtac) (ret I) p prf
    | Nothing =>
      x <- evar;
      y <- evar;

      eq <- unify (x /\ y) p;
      match eq with
      | Some prf =>
        pX <- f x hyps;
        pY <- f y hyps;

        @eq_rect Prop _ Mtac (ret (conj pX pY)) p prf
      | Nothing =>
        x <- evar;
        y <- evar;

        eq <- unify (x \/ y) p;

        match eq with
        | Some prf =>
          try (
            r1 <- f x hyps;

            @eq_rect Prop (x \/ y) Mtac (ret (@or_introl x y r1)) p prf
          ) (
            r2 <- f y hyps;

            @eq_rect Prop (x \/ y) Mtac (ret (@or_intror x y r2)) p prf
          )
        |  Nothing => search p hyps
        end
      end
    end
  .


Fixpoint replicateProp (t : nat) : Prop :=
  match t with
  | 0 => True
  | S n => False \/ replicateProp n
  (* | _ => let xs := replicate x (t - 1) in (x :: xs) *)
  end.


Goal True.
Proof.
  Time run (simple_tauto True (replicateProp 1000) nil) as r.
  Time compile (simple_tauto True (replicateProp 1000) nil) as v.
