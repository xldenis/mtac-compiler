Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Add LoadPath "../examples".

Require Import MtacLite.MtacLite.
Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.

Definition var_match (y : nat) :=
  match y with
  | 0 => ret I
  | _ => fail "not zero"
  end.

Goal True.
  run (evar_match 0) as r.
  compile (evar_match 0) as v.
  compile (evar_match (0 + 0)) as v.