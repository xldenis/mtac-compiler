Module TD9.

Open Scope list_scope.
Require Import Coq.Lists.List.
        
Inductive alpha : Set := M : alpha | I : alpha | U : alpha.
Definition word : Set := list alpha.


Definition word_M : word := M :: nil.

Definition word_MI : word := M :: I :: nil.

Definition word_IU : word := I :: U :: nil.

Definition word_U : word := U :: nil.

Definition word_UU : word := U :: U :: nil. 

Definition word_I : word := I :: nil.

Definition word_III : word := I :: I :: I :: nil.

Inductive lang : word -> Prop :=
    | axiom :
        lang word_MI
    | rule1 : forall x,
        lang (x ++ word_I) -> lang (x ++ word_IU)
    | rule2 : forall x,
        lang (word_M ++ x) -> lang (word_M ++ x ++ x)
    | rule3 : forall x y,
        lang (x ++ word_III ++ y) -> lang (x ++ word_U ++ y)
    | rule4 : forall x y,
                    lang (x ++ word_UU ++ y) -> lang (x ++ y).

Theorem app_nil_l : forall {A : Type} (l: list A), nil ++ l = l.
Proof.
        intros A l.
        induction l ; simpl. reflexivity. reflexivity.
Qed.

Theorem app_comm_cons : forall {A : Type} (x y:list A) (a:A), a :: (x ++ y) = (a :: x) ++ y.
Proof.
        intros A x y a.
        induction x.
        - apply app_nil_l.
        - simpl. reflexivity.
Qed.
        
Theorem app_assoc : forall {A : Type } (l m n :list A), l ++ m ++ n = (l ++ m) ++ n.
Proof. 
        intros A l m n.
        induction l.
        - simpl. reflexivity.
        - simpl. rewrite IHl. reflexivity.
Qed.

Theorem tail_eq : forall { A : Type} (l m: list A) (a b : A), a :: l = b :: m -> l = m.
Proof.
        intros A l m a b H.
        fold (tail (a :: l)).
        rewrite H.
        simpl.
        reflexivity.
Qed.

Theorem head_eq : forall { A: Type} (l m : list A) (a b : A), a :: l = b :: m -> a = b.
Proof.
        intros A l m a b H.
        fold (hd a (a :: l)).
        rewrite H.
        simpl.
        reflexivity.
Qed.

Theorem word_starts_with_m : forall w : word, lang w -> exists w', M :: w' = w.
Proof.
        intros w prop. 
        induction prop.
        - exists word_I. reflexivity.
        - destruct IHprop as [w' wM]. exists (w' ++ word_U). rewrite app_comm_cons. rewrite -> wM. rewrite <- app_assoc. simpl. reflexivity.
        - destruct IHprop as [w' wM]. simpl in wM. simpl in wM. apply tail_eq in wM. exists (w' ++ w'). rewrite wM. simpl. reflexivity.
        - destruct IHprop as [w' wM]. induction x.
                + simpl in wM. discriminate wM.
                + exists (x ++ word_U ++ y). rewrite <- app_comm_cons in wM. apply head_eq in wM. rewrite wM. rewrite <- app_comm_cons. reflexivity.
        - destruct IHprop as [w' wM]. induction x.
                + simpl in wM. discriminate wM.
                + exists (x ++ y). rewrite <- app_comm_cons in wM. apply head_eq in wM. rewrite wM. reflexivity.
Qed.


Inductive Z3 : Set := Z0 : Z3 | Z1 : Z3 | Z2 : Z3.

Example zero : Z3 := Z0.

Definition succ (num : Z3) : Z3 :=
        match num with
        | Z0 => Z1
        | Z1 => Z2
        | Z2 => Z0
        end.

Definition plus (a b : Z3) : Z3 :=
        match (a, b) with
        | (a, Z0) => a
        | (Z0, a) => a
        | (Z1,Z1) => Z2
        | (Z2,Z1) => Z0
        | (Z1,Z2) => Z0
        | (Z2,Z2) => Z1
        end.

Notation "a + b" := (plus a b) (at level 50, left associativity) : z3_scope.
Notation "0" := Z0 : z3_scope.
Notation "1" := Z1 : z3_scope.
Notation "2" := Z2 : z3_scope.

Delimit Scope z3_scope with z3.
Open Scope z3_scope.


Theorem z3_plus_comm : forall (a b : Z3), a + b = b + a.
Proof.
        intros a b.
        induction a; induction b; try (unfold plus); reflexivity.
Qed.

Theorem z3_plus_assoc : forall (a b c : Z3), a + (b + c) = (a + b) + c.
Proof.
        intros a b c.
        induction a; induction b; induction c; unfold plus; reflexivity.
Qed.

Theorem z3_0_left : forall (a : Z3), a + 0 = a.
Proof.
        intros a.
        induction a; unfold plus; reflexivity.
Qed.

Theorem z3_0_right : forall (a : Z3), 0 + a = a.
Proof.
        intros a.
        rewrite z3_plus_comm. apply z3_0_left. 
Qed.

Theorem z3_mod : forall (z : Z3), z <> 0 -> z + z <> 0.
Proof.
        intros z H.
        induction z; unfold plus; try discriminate.
        - assumption.
Qed.

Fixpoint occurI3 (w : word) : Z3 :=
        match w with
        | I :: ws => 1 + occurI3 ws
        | _ :: ws => occurI3 ws
        | nil => 0
        end.

Theorem i_z3_dist : forall (w v : word), occurI3 (w ++ v) = occurI3 w + occurI3 v.
Proof.
        intros w v.
        induction w.
        - simpl. rewrite -> z3_0_right. reflexivity.
        - induction a; simpl; try assumption.
          + simpl. rewrite IHw. rewrite z3_plus_assoc. reflexivity.
Qed.

Theorem words_not_0_i : forall (w : word), lang w -> occurI3 w <> 0.
Proof.
        intros w H.
        induction H.
        - simpl. discriminate.
        - { 
                rewrite i_z3_dist. 
                assert (word_IU = word_I ++ word_U). { simpl. reflexivity. }
                rewrite H0. 
                rewrite z3_plus_assoc.
                rewrite <- i_z3_dist.
                simpl. rewrite z3_0_left. 
                assumption.
        }
        -       repeat (rewrite i_z3_dist). 
                simpl in IHlang. 
                simpl. 
                rewrite z3_0_right. 
                apply z3_mod.
                assumption.
        -       repeat (rewrite i_z3_dist in IHlang).
                assert (occurI3 word_III = 0). simpl. unfold plus. reflexivity.
                rewrite H0 in IHlang.
                rewrite z3_0_right in IHlang.
                repeat (rewrite i_z3_dist).
                simpl. rewrite z3_0_right.
                assumption.
        -       repeat (rewrite i_z3_dist in IHlang).
                simpl. rewrite z3_0_right in IHlang.
                rewrite i_z3_dist.
                assumption.
Qed.

Definition word_MU := M :: U :: nil.

Theorem mu_not_lang : ~ lang (word_MU).
Proof.
        unfold not.
        assert (occurI3 word_MU = 0). simpl. reflexivity.
        intros H0.
        apply words_not_0_i in H0.
        contradiction.
Qed.


        
End TD9.
