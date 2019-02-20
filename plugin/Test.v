Add Rec LoadPath "./_build/default/theories" as MtacLite.
Add ML Path "./_build/default/src".

Require Import MtacLite.MtacLite.

Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.

Check print "pomg".

Definition isAnd (a : Prop) : Mtac bool :=
    x <- evar;
    y <- evar;

    eq <- unify a (x /\ y);
    match eq with
    | Some prf => ret true
    | Nothing => ret false
    end
  .

Notation "'mfix' f ( x : A ) : 'M' T := b" := (fix' (fun x=>T) (fun f (x : A)=>b))
  (at level 85, f at level 0, x at next level, format
  "'[v  ' 'mfix'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'").

Goal True.
Proof.
  compile (print "gmo") as t1.
  compile (ret 1) as t2.
  compile (bind (ret 2) (fun x => ret x)) as t3.
  compile (unify tt tt) as t4.

Admitted.

Goal True.
Proof.
  run (MtacLite.print "omg") as omg.
  run (MtacLite.unify False True) as omg2.
  (*run (tauto_simpl true) as om22.*)
  pose (@eq_refl _ (~ False)).
  unfold not in e.
  simpl in e.
  compile (print "omg2") as tt.
  run (MtacLite.ret 1) as om3.
  run (isAnd (1 = 2 /\ 3 = 2)) as om4.
Qed.