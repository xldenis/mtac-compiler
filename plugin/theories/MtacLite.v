
Require Import Strings.String.

Module MtacLite.

Inductive Mtac : Type -> Type :=
  | print : string -> Mtac unit
  | ret   : forall {A}, A -> Mtac A
  | bind  : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B
  | unify : forall {A B}, A -> B -> Mtac bool
  | fix'  : forall {A B} (S : Type -> Prop), (* Why??? *)
    (forall a, S a -> Mtac a) ->
    ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
    forall x : A, Mtac (B x)
  | fail : forall {A}, string -> Mtac A
  | nu : forall {A B}, (A -> Mtac B) -> Mtac B
  .


(*Definition tactic (A : Type) := goal gs_base -> Mtac (list (prod A (goal gs_any))).*)
End MtacLite.

Declare ML Module "mtaclite".
