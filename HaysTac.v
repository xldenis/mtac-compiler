Require Import Mtac2.Mtac2.
Import T.

Ltac assert_distinct X Y := match X with Y => fail 1 | _ => idtac end.

Ltac assert_same X Y := match X with Y => idtac end.

(** Core/Assert.v *)

Definition massert_distinct {A} (x y : A) : tactic :=
  mmatch x with
  | y => ret (M.raise DoesNotMatch)
  | _ => idtac
  end. (** error is that tactic != gtactic unit ??? *)


Ltac assert_same X Y := match X with Y => idtac end.

Definition massert_same {A} (x y : A) : tactic :=
  mmatch x with
  | y => idtac
  | ret (M.raise DoesNotMatch) (** wrong exception but whatever *)
  end.

(** Core/Get *)
Definition mget_type_of (a : Hyp) : t Type :=
  ?????

