
Require Import Strings.String.

Module MtacLite.

Inductive Mtac : Type -> Type :=
  | print : string -> Mtac unit
  | ret   : forall {A}, A -> Mtac A
  | bind  : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B
  | unify : forall {A} (x y : A) ,Mtac ({ x = y } + {x <> y })
  | fix'  : forall {A B} (S : Type -> Prop), (* Why??? *)
    (forall a, S a -> Mtac a) ->
    ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
    forall x : A, Mtac (B x)
  | fail : forall {A}, string -> Mtac A
  | nu : forall {A B}, (A -> Mtac B) -> Mtac B (*idk if we actually need nu*)
  | evar : forall {A}, Mtac A
  | try : forall {A}, Mtac A -> Mtac A -> Mtac A
  .

(*Definition tactic (A : Type) := goal gs_base -> Mtac (list (prod A (goal gs_any))).*)
End MtacLite.

Export MtacLite.

Module MtacLiteNotations.

  Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2))
    (at level 81, right associativity).
  Notation "t1 ';;' t2" := (@bind _ _ t1 (fun _=>t2))
    (at level 81, right associativity).
End MtacLiteNotations.

Declare ML Module "mtaclite".
