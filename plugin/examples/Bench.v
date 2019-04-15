Add Rec LoadPath "../_build/default/theories" as MtacLite.
Add ML Path "../_build/default/src".

Require Import List.

Import ListNotations.


Fixpoint replicate {A} (t : nat) (x : A) : list A :=
  match t with
  | 0 => nil
  | S n => x :: replicate n x
  (* | _ => let xs := replicate x (t - 1) in (x :: xs) *)
  end.

Module BenchMtacLite.

Require Import MtacLite.MtacLite.

Import MtacLite.MtacLiteNotations.

Import Coq.Strings.String.

Fixpoint inList' { A } (x : A) (ls : list A) : Mtac A :=
  mmatch ls
         [ (nil => fail "omg")%pattern
         ; ([? y ls' ] y :: ls' => fail "omg" )%pattern
         ].


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
