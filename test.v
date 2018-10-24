Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
        intros n m o.
        intros H.
        intros G.
        rewrite -> H.
        rewrite <- G.
        reflexivity.
Qed.

Set Warnings "-notation-overridden,-parsing".

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ (~ P)).
Proof.
        unfold not.
        intros P f.
        apply f.
        right. 
        intro p.
        apply f.
        - left. apply p.
Qed.

Definition excluded_middle := forall P : Prop, P \/ ~ P.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
        intros X P.
        intros allP.
        intros [x nPx].
        apply nPx.
        apply allP.
Qed.


Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
        intros em.
        intros X P H.
        intros x.
        assert (P x \/ ~ P x).
        apply em.
        inversion H0.
        apply H1.
        exfalso.
        apply H.
        exists x.
        apply H1.
Qed.

        
