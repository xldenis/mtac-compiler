Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Add LoadPath "../examples".

Require Import MtacLite.MtacLite.
Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.

Definition tactic_call (y : nat) :=
  ret y.

Definition pure_call (y : nat) :=
  y + y.

Definition mixed_calls (y : nat) :=
  ret (y + y).

Goal True.
  compile (ret I) as x.
  compile (tactic_call 0) as v.
  (*compile (pure_call 0) as v2.*)
  compile (mixed_calls 0) as v3.
  compile (ret (1 + 2)) as v4.
  compile (ret (1 + 2 + 3)) as v5.
  compile (bind (ret (1 + 2)) (fun x => ret x)) as v6.
  compile (ret ((id Nat.add) 1 2 )) as v7.
Admitted.
