Require Import Mtac2.Mtac2.
Import T.

Ltac inject H := injection H; clear H; intros; try subst.

Definition minject {A} (x : A) : tactic :=
  A <- goal_type;
  (injection A) >>= clear;;
  intros_all;;
  try subst.

Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

Definition mappHyps {A B} (f : A -> gtactic B) : gtactic B :=
  match_goal with
  | [[ H : A |- B ]] => f H
  end.


(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

Import Mtac2.lib.List.ListNotations.

Definition minList {A} (x : A) (ls : list A) : tactic :=
  mmatch ls with
    | [? R] x :: R  => idtac
    | [? X R ] X :: R => minList x R
    | nil => fun _ => M.failwith "omg"
  end%list.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.
