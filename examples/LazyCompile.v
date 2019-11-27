Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Add LoadPath ".".

Require Import MtacLite.MtacLite.
Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.
Require Import List.

Import ListNotations.

Lemma or_comm : forall A B, A \/ B <-> B \/ A.
Proof.
  tauto.
Qed.

Print or_comm.

Definition lazyUnify (f : list nat -> list nat -> list nat) (arg : list nat) :=
  x <- evar;
  y <- evar;
  eq <- unify (f x y) arg;
  match eq with
  | Some _ => ret I
  | None => fail "not unifiable"
  end.

Definition lazyUnify' (arg : list nat) :=
  x <- evar;
  y <- evar;
  eq <- unify (app x y) arg;
  match eq with
  | Some _ => ret I
  | None => fail "not unifiable"
  end.


Lemma lazyInterpreter : True.
  run (lazyUnify (@app nat) ([1] ++ [2])).
Qed.

Lemma omg : True.
  compile (unify 1 2) as v.
  Qed.


Lemma lazyCompiler : True.
  (*Fail run (lazyUnify ([1; 2])) as v; exact v.*)
  compile (lazyUnify' ([1] ++ [2])) as v2.
  compile (lazyUnify (@app nat) ([1] ++ [2])) as v. exact v.
Qed.

Definition matchNat (n : nat) :=
  match n with
  | 0 => ret I
  | 1 => ret I
  | _ => fail "too big!"
  end.

Lemma matchCompiler : True.
  (* a what?? *)
  compile (matchNat 1) as v.
Qed.
