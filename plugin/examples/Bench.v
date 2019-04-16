Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Add LoadPath "../examples".
Require Import List.

Import ListNotations.


Fixpoint replicate {A} (t : nat) (x : A) : list A :=
  match t with
  | 0 => nil
  | S n => x :: replicate n x
  (* | _ => let xs := replicate x (t - 1) in (x :: xs) *)
  end.

Require Import TautoExample.
Module BenchMtacLite.

Require Import MtacLite.MtacLite.
Import MtacLite.MtacLiteNotations.
Open Scope M_scope.
Import Coq.Strings.String.

Fixpoint inList' { A } (x : A) (ls : list A) : Mtac A :=
  mmatch ls as ls' return M A with
  | nil => fail "omg"
  | [? y ls' ] y :: ls' => fail "omg"
  end.


Fixpoint inList {A} (x : A) (ls : list A) : Mtac A :=
  match ls with
  | [] => fail "omg"
  | y :: ls' =>
    eq <- unify x y;
    match eq with
    | Some _ => ret x
    | None   => inList x ls'
    end
  end
.

Lemma bench : True.
  run (try (inList' True (replicate 100 False)) (ret False)) as v1.
  Time run (try (inList True (replicate 10000 False)) (ret False)) as v.
  Time compile (try (inList True (replicate 100000 False)) (ret True)) as v2.
  Time compile (try (inList' True (replicate 50000 False)) (ret True)) as v3.
  easy.
Qed.
Include TautoExample.TautoExample.
Lemma b1 {H : Prop} : (True \/ True) \/ ((H -> True) \/ True).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.

Lemma b2 {Q : Prop} : (True /\ True) \/ (True /\ (Q -> Q)).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.

Lemma b3 {W Z M : Prop} : W -> (True /\ ((True /\ W) /\ ((True /\ (Z -> True)) \/ (M -> ((W /\ M) /\ W))))).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.

Lemma b4 {P F B Y U N E I : Prop} :P -> ((F -> ((F \/ (((True \/ (B -> (Y -> (U -> Y)))) \/ True) /\ (F /\ F))) /\ (N -> ((((E -> N) \/ P) /\ (True \/ (I -> ((True /\ True) \/ (True /\ P))))) /\ F)))) \/ ((True \/ True) /\ (P \/ (E -> True)))).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b5 {V G O T : Prop} :((V -> V) \/ True) \/ (True /\ ((G -> ((O -> (T -> T)) \/ G)) \/ True)).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b6 {I : Prop} : ((True \/ ((I -> True) /\ True)) \/ (True /\ (True \/ True))) /\ True.
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b7 {M V H Y C X : Prop} : ((M -> (V -> (H -> ((Y -> (C -> C)) \/ (True /\ (X -> V)))))) /\ True) -> ((M -> (V -> (H -> ((Y -> (C -> C)) \/ (True /\ (X -> V)))))) /\ True).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b8 {M W G : Prop} : M -> (True \/ (W -> (G -> M))).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b9 {S O B V M G H : Prop} : (True /\ (True /\ True)) \/ ((((True /\ True) /\ True) \/ ((S -> True) -> (O -> O))) /\ (B -> (V -> ((S -> (M -> (G -> G))) \/ (H -> V))))).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b10 {W I U P G Y : Prop} : ((((True /\ True) \/ True) /\ (True \/ (True /\ (W -> ((I -> (True /\ ((True /\ W) \/ (True \/ True)))) \/ (I -> (True /\ ((W /\ W) /\ True)))))))) /\ True) /\ ((U -> U) /\ (True /\ (True /\ (True \/ (P -> ((G -> True) /\ (Y -> (P \/ True)))))))).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b11 {U C V Y P K : Prop} : ((U -> True) \/ True) \/ (C -> ((V -> ((Y -> ((P -> (V -> True)) /\ C)) -> ((K -> True) /\ (Y -> ((P -> (V -> True)) /\ C))))) /\ True)).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b12 {D : Prop} : True \/ (((D -> True) \/ True) \/ True).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.
Lemma b13 {W V A E D S : Prop} : True \/ (((True /\ ((W -> (True /\ (True /\ (True \/ ((True /\ W) \/ (V -> W)))))) /\ True)) /\ (True \/ ((A -> True) /\ (((E -> (D -> True)) \/ (V -> (True \/ (True \/ (S -> True))))) /\ True)))) /\ True).
Proof.
  match goal with
  |- ?g => compile (simple_tauto g []) as v;
           compile (simple_tauto' g []) as v2;
           run (simple_tauto g []) as v3
  end.
  easy.
  Unshelve. all: easy.
Qed.

End BenchMtacLite.

Module BenchMtac2.
Require Import Mtac2.Mtac2.
Import T.

Require Import Lists.List.
Import Lists.List.ListNotations.
Import Mtac2.lib.List.ListNotations.

Fixpoint inList {A} (x : A) (ls : mlist A) : tactic :=
  match ls with
  | [m:] => fun _ => M.failwith "omg"
  | y :m: ls' => mmatch y with
          | x => idtac
          | _ => minList x ls'
  end
end.
End.
