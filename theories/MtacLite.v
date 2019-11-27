Require Import List.

Require Import Strings.String.

Module MtacLite.

Definition callType {A : Type} (a : A) := a.

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

Inductive pattern (A : Type) (B : A -> Type) (y : A) : Prop :=
  (* apparently this should be Mtac (B x) *)
  | pbase : forall x : A, (y = x -> Mtac (B x)) -> pattern A B y
  | ptele : forall {C:Type}, (forall x : C, pattern A B y) -> pattern A B y.

Arguments pbase {A B y} _ _ .

Arguments ptele {A B y C} _.

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

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.

Notation "p => b" := (pbase p%core (fun _ => b%core))
  (no associativity, at level 201) : pattern_scope.

Delimit Scope pattern_scope with pattern.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((cons p1%pattern (.. (cons pn%pattern nil) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

End MtacLiteNotations.

Import ListNotations.
Import MtacLiteNotations.

Fixpoint open_pattern {A P y} (p : pattern A P y) : Mtac (P y) :=
  match p with
  | pbase x f =>
      eq <- unify x y;
      match eq return Mtac (P y) with
      | Some prf =>
        let z := f (eq_sym prf) in match prf with eq_refl => z end
      | None => fail "no match: branch"
      end
  | ptele f => e <- evar; open_pattern (f e)
  end.

Fixpoint mmatch' {A P} (y : A) (ps : list (pattern A P y)) :=
  match ps with
  | nil => fail "no match"
  | p :: ps' => try (open_pattern p) (mmatch' y ps')
  end.

Notation "'mmatch' x 'as' y 'return' 'M' p ls" :=
  (@mmatch' _ (fun y => p%type) x ls%with_pattern)
  (at level 200, ls at level 91) : M_scope.
Delimit Scope M_Scope with M.

End MtacLite.

Export MtacLite.

Declare ML Module "mtaclite".
