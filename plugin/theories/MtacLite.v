Declare ML Module "mtaclite".

Require Import Strings.String.

Module MtacLite.

Inductive Mtac : Type -> Prop :=
  | print : string -> Mtac unit
  | tret : forall {A}, A -> Mtac A
  | bind : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B.

End MtacLite.

(*Export MtacLite.
*)
