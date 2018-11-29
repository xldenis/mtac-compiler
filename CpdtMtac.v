Require Import Mtac2.Mtac2.
Import T.

Require Import Lists.List.
Import Lists.List.ListNotations.
Import Mtac2.lib.List.ListNotations.

Require Import Eqdep List Omega.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Definition minject {A} (x : A) : tactic :=
  A <- goal_type;
  (injection A) >>= clear;;
  intros_all;;
  try subst.

Definition mappHyps {A B} (f : A -> gtactic B) : gtactic B :=
  match_goal with
  | [[ H : A |- B ]] => f H
  end.

(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Fixpoint minList {A} (x : A) (ls : list A) : tactic :=
        match ls with
        | nil => fun _ => M.failwith "omg"
        | y :: ls' => mmatch y with
                | x => idtac
                | _ => minList x ls'
        end
end%list.


(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
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
Fixpoint mall {A} (f : A -> tactic) (ls : mlist A) : tactic :=
  match ls with
  | [m:] => fun _ => M.failwith "empty list"
  | x :m: ls' => f x ;; mall f ls'
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
Definition mrewriteHyp : tactic := T.ltac (qualify "rewriteHyp") [m:].

(** Combine [autorewrite] with automatic hypothesis rewrites. *)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Definition mrewriterP : tactic := T.ltac (qualify "rewriteP") [m:].

Ltac rewriter := autorewrite with core in *; rewriterP.
Definition mrewriter : tactic := T.ltac (qualify "rewriter") [m:].

(** This one is just so darned useful, let's add it as a hint here. *)
Hint Rewrite app_ass.

(** Devious marker predicate to use for encoding state within proof goals *)
Definition done {A} (x : A) := True.

Set Implicit Arguments.
Set Printing All.

(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. *)
Fixpoint minster (e : dyn) (trace : mlist dyn) : tactic :=

  mmatch e with
  | [? (X : Type)  (G : X -> Type) (F : _ )]  @Dyn (forall x : X, G x) F  => match_goal with
        | [[H : X |- _ ]] => minster (Dyn (F H)) (Dyn H :m: trace)
        end
  | _ =>
  mmatch (M.type_of e) with
    | [!Type] forall _ : X, P  =n> idtac

    | _ =>
        match trace with
        | _ :m: _  =>
            match_goal with
            | [[? B G | H : done (m: trace, B) |- G ]] => raise GoalNotExistential (** replace w better exception *)
            | _ =>
              let T := M.type_of e in
                mmatch (M.type_of T) with
                  | Prop => idtac  (*generalize e &> intro H &> assert (done (m: trace, tt)) by constructor*)
                  | _ =>
                    mall (fun (X : dyn) =>
                      match_goal with
                      | [[? A G | H : done (A, X) |- G ]] => raise GoalNotExistential
                      (*| _ => idtac*)
                      end) trace ;;
                      idtac
                    (*let i := fresh "i" in (pose (i := e) &> assert (done (trace, i)) by constructor)*)
                end
            end
        | [m:] => raise GoalNotExistential
       end%list
    end
  end.


(** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

(** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
Definition un_done : tactic :=
  repeat (match_goal with
           | [ H : done _ |- _ ] => clear H
         end).

Require Import JMeq.


(** A more parameterized version of the famous [crush].  Extra arguments are:
   * - A tuple-list of lemmas we try [inster]-ing
   * - A tuple-list of predicates we try inversion for *)
Ltac crush' lemmas invOne :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intuition; try subst;
    repeat (simplHyp invOne; intuition; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush' lemmas invOne
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
      match lemmas with
        | false => idtac (** No lemmas?  Nothing to do here *)
        | _ =>
          (** Try a loop of instantiating lemmas... *)
          repeat ((app ltac:(fun L => inster L L) lemmas
          (** ...or instantiating hypotheses... *)
            || appHyps ltac:(fun L => inster L L));
          (** ...and then simplifying hypotheses. *)
          repeat (simplHyp invOne; intuition)); un_done
      end;
      sintuition; rewriter; sintuition;
      (** End with a last attempt to prove an arithmetic fact with [omega], or prove any sort of fact in a context that is contradictory by reasoning that [omega] can do. *)
      try omega; try (elimtype False; omega)).


(** A more parameterized version of the famous [crush].  Extra arguments are:
   * - A tuple-list of lemmas we try [inster]-ing
   * - A tuple-list of predicates we try inversion for *)
Definition crush' (lemmas : mlist dyn) (invOne : mlist dyn) : tactic :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in * &> intuition &> try subst &>
    repeat (simplHyp invOne &> intuition &> try subst) &> try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in * &>
    repeat (match_goal with
              | [[? P | H : P |- _ ]] =>
                match P with
                  | context[JMeq] => raise 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush' lemmas invOne
                end
            end &> autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition &> rewriter &>
      match lemmas with
        | nil => idtac (** No lemmas?  Nothing to do here *)
        | _ =>
          (** Try a loop of instantiating lemmas... *)
          repeat ((app (fun L => inster L L) lemmas
          (** ...or instantiating hypotheses... *)
            || appHyps (fun L => inster L L)) &>
          (** ...and then simplifying hypotheses. *)
          repeat (simplHyp invOne; intuition)) &> un_done
      end &>
      sintuition &> rewriter &> sintuition &>
      (** End with a last attempt to prove an arithmetic fact with [omega], or prove any sort of fact in a context that is contradictory by reasoning that [omega] can do. *)
      try omega &> try (elimtype False &> omega)).
