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

module Constr = struct
  exception Constr_not_found of string
  exception Constr_poly of string

  let mkConstr name = lazy (
    try Universes.constr_of_global
    (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)
      | Invalid_argument _ -> raise (Constr_poly name)
  )

  let mkUConstr name sigma env =
    try Evd.fresh_global env sigma
    (Nametab.global_of_path (Libnames.path_of_string name))
    with Not_found -> raise (Constr_not_found name)

  let isConstr = fun r c -> eq_constr (Lazy.force r) c

  let isUConstr r sigma env = fun c ->
    eq_constr_nounivs (snd (mkUConstr r sigma env)) c

  let eq_ind i1 i2 = Names.eq_ind (fst i1) (fst i2)

end

open Constr
module CoqUnit = struct
  let mkTT : constr lazy_t = Constr.mkConstr "Coq.Init.Datatypes.tt"
end

let nowhere = Locus.({ onhyps = Some []; concl_occs = NoOccurrences })

let run_tac t i   =
  Proofview.Goal.enter begin fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let env = Proofview.Goal.env gl in
    (Tactics.letin_tac None (Name i) (EConstr.of_constr (Lazy.force CoqUnit.mkTT)) None Locusops.nowhere)
  end


TACTIC EXTEND run
  | [ "run" constr(c) "as" ident(i) ] -> [ run_tac c i ]
END
