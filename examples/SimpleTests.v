Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Add LoadPath "../examples".

Require Import MtacLite.MtacLite.
Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.

Goal True.
  compile (fail "str" : Mtac unit) as r.
