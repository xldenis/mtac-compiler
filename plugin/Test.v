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


Notation "'mfix' f ( x : A ) : 'M' T := b" := (fix' (fun x=>T) (fun f (x : A)=>b))
  (at level 85, f at level 0, x at next level, format
  "'[v  ' 'mfix'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Definition simpl_prop_auto :=
  mfix f (p : Prop) : M (p : Prop) := (* problem is here*)
    fail "omg"
  .

Definition tauto_simpl (prop : Prop) : Mtac prop :=
    mfix f (x : Prop) : M (x : Prop) :=
      fail "omg"

     .
Goal True.
Proof.
 run (MtacLite.print "omg") as omg.
 run (MtacLite.unify False True) as omg2.
 run (tauto_simpl True) as om22.

 run (MtacLite.ret 1) as om3.
 exact om22.
 (*run (isAnd (1 = 2 /\ 3 = 2)) as om4.*)
