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

Definition pure_impure (a : Mtac bool) (b : bool) : Mtac bool :=
  a' <- a ;
  ret b.

Definition pure_impure2 (a : Mtac bool) (b : bool) : Mtac bool :=
  a' <- a ;
  ret a'.

Lemma cbn_compile : True.
Proof.
  (* figure out why I can't run compile twice in the same session. *)
  run (ret (fun (x : nat) => id x)) as y.
  run (unify (5 + 2) 7) as y1.
  compile (pure_impure  (ret (orb true false)) (orb false true)) as x.
  compile (pure_impure  (ret (orb true false)) (orb false true)) as x'.
  compile (pure_impure2 (ret (orb true false)) (orb false true)) as x2.
  (* compile (List.map) as x2. *)
  compile (ret (5 + 2)) as x3.
Qed.


Goal True.
Proof.
  run (nu (fun (x : id True) => abs x (ret I))) as x.
  compile (nu (fun (x : id True) => abs x (ret I))) as x2.

  compile (ret (fun (x : Prop) => id x)) as v.
  run (ret (fun (x : Prop) => id x)) as v2.
Qed.

Goal True.
Proof.
  run (nu (fun (x : Prop) => abs x (ret x))) as x.
  compile (nu (fun (x : Prop) => abs x (ret x))) as x2.
Admitted.

Goal True.
Proof.
  compile (print "gmo") as t1.
  compile (ret 1) as t2.
  compile (bind (ret 2) (fun x => ret x)) as t3.
  compile (unify tt tt) as t4.
Admitted.

Lemma compile_evar : True.
Proof.
  compile (@evar nat) as t1.
  run (@evar nat) as r1.
  compile (ret t1) as c.
Admitted.

Lemma unify_vars : True.
Proof.
  run (@evar Prop) as e1.
  run (@evar Prop) as e2.
  run (unify (True \/ False) (e1 \/ e2)) as t1.
Admitted.

Lemma test_evar_unify : True.
  run (x <- @evar Prop ; ret (fun y => unify x y ;; ret y)) as t.
  compile (nu (fun (x : Prop) => abs x (ret x))) as o.
Goal True.
Proof.
  run (MtacLite.print "omg") as omg.
  run (MtacLite.unify False True) as omg2.
  run (tauto_simpl true) as om22.
  pose (@eq_refl _ (~ False)).
  unfold not in e.
  simpl in e.
  compile (print "omg2") as tt.
  run (MtacLite.ret 1) as om3.
  run (isAnd (1 = 2 /\ 3 = 2)) as om4.
Qed.
