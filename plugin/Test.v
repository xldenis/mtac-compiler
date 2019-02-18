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

Goal True.
Proof.
  compile (print "omg") as t1.
  compile (ret 1) as t2.
  compile (bind (ret 1) (fun x => ret x)) as t3.

Admitted.

Goal True.
Proof.
  run (MtacLite.print "omg") as omg.
  run (MtacLite.unify False True) as omg2.
  run (tauto_simpl True) as om22.
  pose (ret tt2) as om222.
  native_compute in om222.
  compile (print "omg") as tt.
  run (MtacLite.ret 1) as om3.
  exact om22.
  run (isAnd (1 = 2 /\ 3 = 2)) as om4.
