Add Rec LoadPath "./theories" as MtacLite.
Add ML Path "./src".

Require Import MtacLite.MtacLite.

Check MtacLite.print "pomg".

Goal True.
Proof.
 run (MtacLite.print "omg") as omg.
 run (MtacLite.unify False True) as omg2.
 run (MtacLite.ret 1) as om3.