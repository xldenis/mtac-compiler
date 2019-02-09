Add Rec LoadPath "./theories" as MtacLite.
Add ML Path "./src".

Require Import MtacLite.MtacLite.

Import MtacLite.MtacLiteNotations.

Check print "pomg".

Definition isAnd (a : Prop) : Mtac bool :=
    x <- evar;
    y <- evar;

    eq <- unify a (x /\ y);
    match eq with
    | left prf => ret true
    | right prf => ret false
    end
  .

  Definition tauto_simpl (prop : Prop) : Mtac prop :=
    isT <- unify True prop;
    match isT with
    | left prf => @eq_rect Prop True (Mtac) (ret I) prop prf
    | right _ => fail "omg"
    end
     .
Goal True.
Proof.
 run (MtacLite.print "omg") as omg.
 run (MtacLite.unify False True) as omg2.
 run (tauto_simpl True) as om22.
 
 run (MtacLite.ret 1) as om3.
 exact om22.
 (*run (isAnd (1 = 2 /\ 3 = 2)) as om4.*)
