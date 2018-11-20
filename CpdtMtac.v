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

(** Devious marker predicate to use for encoding state within proof goals *)
Definition done (T : Type) (x : T) := True.


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

(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. *)
Ltac inster e trace :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Abort to backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>
                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

Fixpoint minster (e : dyn) (trace : mlist dyn) : tactic :=
  mmatch (M.type_of e) with
    | [!Type] forall _ : X, P  =n>
        match_goal with
        (**  how do we 'refine' the type of e? *)
        | [[ H : _ |- _ ]] => minster (e H) (H :m: trace)
        end
    | _ =>
        match trace with
        | _ :: _  =>
            match_goal with
            | [[H : done (trace, _) |- _ ]] => raise GoalNotExistential (** replace w better exception *)
            | _ =>
              let T := M.type_of e in
                mmatch (M.type_of T) with
                  | Prop => idtac  (*generalize e &> intro H &> assert (done (m: trace, tt)) by constructor*)
                  | _ =>
                    all (fun X =>
                      match_goal with
                      | [[ H : done (_, X) |- _ ]] => raise GoalNotExistential
                      | _ => idtac
                      end) trace ;;
                      idtac
                    (*let i := fresh "i" in (pose (i := e) &> assert (done (trace, i)) by constructor)*)
                end
            end
        end%list
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
