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

            @eq_rect Prop (x \/ y) Mtac (ret (or_introl r1)) p prf
          ) (
            r2 <- f y;

            @eq_rect Prop (x \/ y) Mtac (ret (or_intror r2)) p prf
          )
         | Nothing => fail "Not Found"
        end
      end
    end
  .

Check simple_tauto.

Definition is_or :=
  mfix f (p : Prop) : M p :=
    x <- evar;
    y <- evar;

    eq <- unify (x \/ y) p;

    match eq with
    | Some prf =>
      try (
        r1 <- f x;

        @eq_rect Prop (x \/ y) Mtac (ret (or_introl r1)) p prf
      ) (
        r2 <- f y;

        @eq_rect Prop (x \/ y) Mtac (ret (or_intror r2)) p prf
      )
    | Nothing =>
      eq <- unify True p;
      match eq with
      | Some prf => @eq_rect Prop True Mtac (ret I) p prf
      | None => fail "Not found"
      end
    end
  .


Goal True \/ False.
Proof.
  run (is_or (True \/ (True \/ False))).
Qed.

Example ex0 : True \/ False.
Proof.
  run (simple_tauto (True \/ False)).
Qed.

Example ex1 : True /\ (False \/ True).
Proof.
  run (simple_tauto (True /\ (False \/ True))).
Qed.

