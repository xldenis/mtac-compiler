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
    Refine.refine (fun sigma ->
    let env : Environ.env = Proofview.Goal.env gl in
    let goal : EConstr.t = Proofview.Goal.concl gl in
    let result = Run.interpret env sigma goal t in
    match result with
    | Val (_, s, c) -> (s, Lazy.force c)
    | Err (_, _, _) -> failwith "FAILURE!" (* figure out how to raise errors to coq nicely *)
    ) ~typecheck:true
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
END
