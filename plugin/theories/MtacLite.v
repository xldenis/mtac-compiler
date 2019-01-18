
Require Import Strings.String.

Module MtacLite.

Inductive Mtac : Type -> Type :=
  | print : string -> Mtac unit
  | tret : forall {A}, A -> Mtac A
  | bind : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B
  | unify : forall {A B}, A -> B -> Mtac unit.


End MtacLite.

Declare ML Module "mtaclite".
