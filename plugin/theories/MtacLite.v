
Require Import Strings.String.

Module MtacLite.

Inductive Mtac : Type -> Prop :=
  | print : string -> Mtac unit
  | ret   : forall {A}, A -> Mtac A
  | bind  : forall {A B}, Mtac A -> (A -> Mtac B) -> Mtac B
  | unify : forall {A} (x y : A) , Mtac (option (x = y))
  | fix'  : forall {A B} (S : Prop -> Prop),
    (forall a, S a -> Mtac a) ->
    ((forall x : A, S (B x)) -> (forall x : A, S (B x))) ->
    forall x : A, Mtac (B x)
  | fail : forall {A}, string -> Mtac A
  | nu : forall {A B}, (A -> Mtac B) -> Mtac B (*idk if we actually need nu*)
  | evar : forall {A}, Mtac A
  | try : forall {A}, Mtac A -> Mtac A -> Mtac A
  | abs : forall {A P} (x : A), P x -> Mtac (forall x, P x)
  .

End MtacLite.

Export MtacLite.

Module MtacLiteNotations.

  Notation "r '<-' t1 ';' t2" := (@bind _ _ t1 (fun r=> t2))
    (at level 81, right associativity).
  Notation "t1 ';;' t2" := (@bind _ _ t1 (fun _=>t2))
    (at level 81, right associativity).

  Notation "'mfix' f ( x : A ) : 'M' T := b" :=
    (@fix' A (fun x => T) Mtac (fun _ (x : Mtac _) => x) (fun f (x : A) => b))
    (at level 85, f at level 0, x at next level, format
    "'[v  ' 'mfix'  f  '(' x  ':'  A ')'  ':'  'M'  T  ':=' '/  ' b ']'").

End MtacLiteNotations.

Declare ML Module "mtaclite".
