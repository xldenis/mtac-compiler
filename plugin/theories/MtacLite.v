
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
  | fix2' : forall {A1 A2 B} (S : Prop -> Prop),
    (forall a, S a -> Mtac a) ->
    ((forall (x1 : A1) (x2 : A2 x1), S (B x1 x2)) ->
      (forall (x1 : A1) (x2 : A2 x1), S (B x1 x2))) ->
    forall (x1 : A1) (x2 : A2 x1), Mtac (B x1 x2)
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

Notation "'mfix2' f ( x : A ) ( y : B ) : 'M' T := b" :=
  (@fix2' A (fun x=>B%type) (fun (x : A) (y : B)=>T) Mtac (fun _ x => x) (fun f (x : A) (y : B)=>b))
  (at level 85, f at level 0, x at next level, y at next level, format
  "'[v  ' 'mfix2'  f  '(' x  ':'  A ')'  '(' y  ':'  B ')'  ':'  'M'   T  ':=' '/  ' b ']'").

End MtacLiteNotations.

Declare ML Module "mtaclite".
