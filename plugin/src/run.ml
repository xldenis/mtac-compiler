open Term
open Names
open Coqlib

let find_constant dir s = EConstr.of_constr (
  Universes.constr_of_global (Coqlib.find_reference "mtac_plugin" dir s)
)

open EConstr

module CoqUnit = struct
  let mkTT : constr lazy_t = lazy (find_constant ["Coq"; "Init"; "Datatypes"] "tt")
end



module CoqTerm = struct
  let path = ["MtacLite"; "MtacLite"; "MtacLite"]
  let mtacPrint = lazy (find_constant path "print")
  let mtacBind  = lazy (find_constant path "bind")
  let mtacRet   = lazy (find_constant path "ret")
  let mtacUnify = lazy (find_constant path "unify")
end

let coq_true = lazy (find_constant ["Init"; "Datatypes"] "true")

(* the objective here is to write the interpreter for mtaclite. Afterwards I'll write the compiler *)

open CoqTerm

let rec reify env sigma constr =
  let hs, args = decompose_app sigma constr in
  match args with
    | [f] when eq_constr sigma hs (Lazy.force mtacPrint) -> CoqUnit.mkTT
    | [a; b] when eq_constr sigma hs (Lazy.force mtacUnify) -> CoqUnit.mkTT
    | [a; b] when eq_constr sigma hs (Lazy.force mtacBind) -> CoqUnit.mkTT
    | [a] when eq_constr sigma hs (Lazy.force mtacRet) -> CoqUnit.mkTT
    | _ -> coq_true
