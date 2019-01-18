(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)


open Ltac_plugin
open Stdarg

DECLARE PLUGIN "mtaclite"

(* $$ *)

open Term
open Names
open Coqlib
open Proofview.Notations
(* $$ *)

open Run

let nowhere = Locus.({ onhyps = Some []; concl_occs = NoOccurrences })

(* val run_tac : EConstr.t -> Names.Id.t -> Proofview.tactic *)
let run_tac t i   =
  Proofview.Goal.enter begin fun gl ->
    let sigma : Evd.evar_map = Proofview.Goal.sigma gl in
    let env : Environ.env = Proofview.Goal.env gl in
    let c = Run.reify env sigma t in
    (Tactics.letin_tac None (Name i) (Lazy.force c) None Locusops.nowhere)
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
END
