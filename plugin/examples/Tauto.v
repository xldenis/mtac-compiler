Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Require Import MtacLite.MtacLite.

Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.
Require Import List.

Import ListNotations.

Record dyn := Dyn { prop : Prop ; elem : prop }.

Definition search (P : Prop) :=
  mfix f (s:list dyn) : M P :=
    match s with
    | Dyn A x :: s' =>
      eq <- unify A P;
        match eq with
        | Some prf => @eq_rect Prop _ Mtac (ret x) P prf
        | Nothing => f s'
        end
    | nil => fail "empty"
    end.


Definition simple_tauto :=
  mfix2 f (p : Prop) (hyps : list dyn) : M p :=
    eq <- unify True p;

    match eq with
    | Some prf => @eq_rect Prop True (Mtac) (ret I) p prf
    | Nothing =>
      x <- evar;
      y <- evar;

      eq <- unify (x /\ y) p;
      match eq with
      | Some prf =>
        pX <- f x hyps;
        pY <- f y hyps;

        @eq_rect Prop _ Mtac (ret (conj pX pY)) p prf
      | Nothing =>
        x <- evar;
        y <- evar;

        eq <- unify (x \/ y) p;

        match eq with
        | Some prf =>
          try (
            r1 <- f x hyps;

            @eq_rect Prop (x \/ y) Mtac (ret (@or_introl x y r1)) p prf
          ) (
            r2 <- f y hyps;

            @eq_rect Prop (x \/ y) Mtac (ret (@or_intror x y r2)) p prf
          )
        | Nothing =>
          q1 <- @evar Prop;
          q2 <- @evar Prop;

          eq <- unify (q1 -> q2) p;
          match eq with
          | Some prf =>
            omg <- nu (fun (a : q1) =>
              a' <- f q2 (Dyn _ a :: hyps);
              abs a a');
            @eq_rect Prop (q1 -> q2) Mtac (ret omg) p prf

          | Nothing =>
            X <- evar;
            Q <- @evar (X -> Prop);

            eq <- unify (exists x : X, Q x) p;

            match eq with
            | Some prf =>
              x <- @evar X;
              q <- f (Q x) hyps;

              @eq_rect Prop (exists x, Q x) Mtac (ret (ex_intro Q x q)) p prf
            | Nothing =>
                A <- @evar Prop;
                Q <- @evar Prop;

                eq <- unify (forall x: A, Q) p;
                match eq with
                | Some prf =>
                  omg <- nu (fun (a : A) =>
                               q' <- f Q hyps;
                               abs a q'

                            );
                  @eq_rect Prop (forall x : A, Q) Mtac (ret omg) p prf
                | Nothing => search p hyps
                end
            end
          end

        end
      end
    end
  .

Check simple_tauto.

Definition simple_fix :=
  mfix f (p : nat) : M True :=
    match p with
    | 0 => ret I
    | n => f (n - 1) ;; f (n - 1)
    end
  .


Example fix_ex : True.
Proof.
  compile (simple_fix 2) as v.
  exact v.
Qed.

(*   run (is_or (True \/ (True \/ False))). *)
(* Qed. *)

Example ex0 : True \/ False.
Proof.
  run (simple_tauto (True \/ False) []).
  all: (exact True).
Qed.

Example ex1 : True.
  run (simple_tauto True []) as v.
  exact v.
Qed.


Example ex2 : True /\ True.
Proof.
  compile (simple_tauto (True /\ True) []) as v.
  exact v.
  Unshelve.
  all: exact True.
Qed.

Example ex3 : True /\ (False \/ True).
Proof.
  compile (simple_tauto (True /\ (False \/ True)) []) as v.
  exact v.
  Unshelve.
  all: (exact True).
Qed.

Example implication : True -> (False \/ True).
Proof.
  run (simple_tauto (True -> False \/ True) []).
  all: exact True.
Qed.

Example existential : exists x, False \/ x.
Proof.
  run (simple_tauto (exists x, False \/ x) []).
  all: exact True.
Qed.

Example implication2 {A : Prop} : A -> A.
Proof.
  run (simple_tauto (A -> A) []).
  all: easy.
Qed.

Example ex_with_implication (p q : Prop) : p -> q -> p /\ q.
Proof.
  run (simple_tauto (p -> q -> p /\ q) []).
  all: easy.
Qed.

Example implication4 {F G : Prop} : (F -> G) -> F -> G.
Proof.
  run (simple_tauto ((F -> G) -> F -> G) []).
  all: easy.
Qed.

Example implication3 : forall (F G : Prop),  (F -> G) -> F -> G.
Proof.
  run (simple_tauto (forall (F G : Prop), (F -> G) -> F -> G) []).
  all: easy.
Example less_complex: forall x (F G : Prop -> Prop), (G x -> F x) -> G x -> F x.
Proof.
  run (simple_tauto (forall x (F G : Prop -> Prop), (G x -> F x) -> G x -> F x) []).
  all: easy.
Qed.

Example ex1 {A B C D : Prop}: (A -> A) /\ (B -> B) \/ (A -> B -> C -> D -> (C \/ D) /\ (A \/ B /\ (C -> D))).
  match goal with
  | |- ?g => compile (simple_tauto g []) as v; exact v
  end.
Qed.


Ex(*ample complex {F G : Prop -> Prop}:
  exists y z, forall x, ((F x -> G y) /\ (G z -> F x)) -> forall x, exists y, (F x -> G y /\ G y -> F x).
Proof.
  run (simple_tauto (exists y z, forall x, ((F x -> G y) /\ (G z -> F x)) -> forall x, exists y, (F x -> G y /\ G y -> F x)) []).*)
