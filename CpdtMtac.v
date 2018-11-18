Require Import Mtac2.Mtac2.
Import T.

Require Import Lists.List.
Import Lists.List.ListNotations.

Require Import Eqdep List Omega.


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

Fixpoint minList {A} (x : A) (ls : list A) : tactic :=
        match ls with
        | nil => fun _ => M.failwith "omg"
        | y :: ls' => mmatch y with
                | x => idtac
                | _ => minList x ls'
        end
end%list.


(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

Fixpoint mapp {A} (f : A -> tactic) (ls : list A) : tactic :=
  match ls with
  | nil => fun _ => M.failwith "empty list"
  | x :: ls' =>
    mtry
      f x
    with
    | _ => mapp f ls'
    end
  end%list.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

Fixpoint mall {A} (f : A -> tactic) (ls : list A) : tactic :=
  match ls with
  | nil => fun _ => M.failwith "empty list"
  | x :: ls' => f x ;; mall f ls'
  end%list.

(** Workhorse tactic to simplify hypotheses for a variety of proofs.
   * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
Ltac simplHyp invOne :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
    (** We only proceed for those predicates in [invOne]. *)
    inList F invOne;
    (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
      (inversion H; fail)
    (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
      || (inversion H; [idtac]; clear H; try subst) in

  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.


(** Workhorse tactic to simplify hypotheses for a variety of proofs.
   * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
Definition msimplHyp (invOne : list dyn) : tactic :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert {B} (H : B) (F : dyn) : tactic :=
    (** We only proceed for those predicates in [invOne]. *)
    minList F invOne &>

    (inversion H &> raise GoalNotExistential)

    || inversion H &> [m: idtac] &> clear H &> try subst

  in match_goal with
  (** Eliminate all existential hypotheses. *)
  | [[? C D | H : ex (C : Type -> Prop) |- (D : Prop) ]] => destruct H
  (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
  | [[? (F : Type -> Prop) (X : Type) (Y : Type) G | (H : F X = F Y) |- G]] =>
    (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
    (assert (_ : X = Y) &> [m: assumption | raise GoalNotExistential ])
    (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
       * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
    || (injection H &> match_goal with
        | [[ |- X = Y -> G ]] => idtac
          (* try (clear H) &> intros &> try subst *)
      end)

  | [[? (F : Type -> Type -> Prop) X Y U V G | H : F (X : Type) (U : Type) = F (Y : Type) (V : Type) |- G ]] =>
      (assert (_ : X = Y) &> [m: assumption
        | assert (_ : U = V) &> [m: assumption | raise GoalNotExistential ] ])
      || (injection H &>
        match_goal with
          | [[ |- U = V -> X = Y -> G ]] =>
            try (clear H) &> intros &> try subst
        end)

  (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
  | [[? (A : Type) (F : A -> Prop) (X : A) (G : Prop) | H : F X        |- G ]] => invert H (Dyn F)
  | [[? (A : Type) (B : A -> Type) (X : A) (Y : B X) (F : forall (X : A), B X -> Prop) (G : Prop) | H : F X Y      |- G ]] => invert H (Dyn F)
  | [[? (A : Type) (B C : A -> Type)
        (X : A) (Y : B X) (Z : C X)
        (F : forall (X : A), B X -> C X -> Prop)
        (G : Prop)
    | H : F X Y Z     |- G ]] => invert H (Dyn F)
  | [[? (A : Type) (B C D : A -> Type)
        (X : A) (Y : B X) (Z : C X) (W : D X)
        (F : forall (X : A), B X -> C X -> D X -> Prop)
        (G : Prop)
    | H : F X Y Z W   |- G ]] => invert H (Dyn F)
  (*| [[? F | H : F _ _ _ _ _ |- _ ]] => invert H (Dyn F)*)


  (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
  | [[? (A : Type) (T : A -> Type) (X Y : A) (L : T X) (M : T X) (G : Prop) | H : existT T X L = existT T X M |- G ]] =>  generalize (inj_pair2 _ _ _ _ _ H) &> clear H 

(**
  (** f we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
  | [[ H : existT _ _ _ = existT _ _ _ |- _ ]] => inversion H &> clear H

  (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
  | [[? (X : Type) (Y : Type) (G : Prop) | H : Some X = Some Y |- G ]] => injection H &> clear H
*)
  end.

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(*Definition mrewriteHyp : tactic :=
  match_goal with
    | [[ H: _ |- _ ]] => rewrite H by solve [ auto ]
  end.
*)

