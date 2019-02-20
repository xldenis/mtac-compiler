Add Rec LoadPath "./_build/default/theories" as MtacLite.
Add ML Path "./_build/default/src".

Require Import MtacLite.MtacLite.

Import MtacLite.MtacLiteNotations.

(*Check print "pomg".*)

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

Lemma True_neq_False : (True <> False).
Proof.
  unfold not.
  intros.
  rewrite <- H.
  exact I.
Qed.

Set Printing All.

Print True_neq_False.

Check eq_ind.

Lemma True_eq_True : (True = True).
  run (unify True True) as omg.
  destruct omg.

  - exact e.
  - contradiction.
Qed.


(*   run (unify True False) as omg. *)
(*   destruct omg. *)
(*   - exfalso. rewrite <- e. exact I. *)
(*   - exact n. *)
(* Qed. *)

Print True_neq_False.
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
  native_compute in om222.
  compile (print "omg2") as tt.
  run (MtacLite.ret 1) as om3.
  exact om22.
  run (isAnd (1 = 2 /\ 3 = 2)) as om4.


