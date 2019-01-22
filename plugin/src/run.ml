open Term
open Names
open Coqlib
open Reductionops

let find_constant dir s = EConstr.of_constr (
  Universes.constr_of_global (Coqlib.find_reference "mtac_plugin" dir s)
)

open EConstr

module CoqUnit = struct
  let mkTT : constr lazy_t = lazy (find_constant ["Coq"; "Init"; "Datatypes"] "tt")
end

module CoqBool = struct
  let mkTrue = find_constant ["Coq"; "Init" ; "Datatypes"] "true"
  let mkFalse = find_constant ["Coq"; "Init" ; "Datatypes"] "false"

  let isTrue sigma o = eq_constr sigma (mkTrue) o
end

module CoqAscii = struct
  let from_coq env sigma c =
    let (h, args) = whd_all_stack env sigma c in
    let rec from_bits n bits =
      match bits with
        | [] -> 0
        | (b :: bs) -> (if CoqBool.isTrue sigma b then 1 else 0) lsl n + from_bits (n+1) bs
    in
    let n = from_bits 0 args in
    Char.escaped (Char.chr n)
end

module CoqString = struct

  let mkEmpty = find_constant  ["Coq"; "Strings" ; "String"] "EmptyString"
  let mkString = find_constant ["Coq"; "Strings" ; "String"] "String"

  let isEmpty sigma o  = eq_constr sigma (mkEmpty) o
  let isString sigma o = eq_constr sigma (mkString) o

  (* let isEmpty = Constr.isConstr mkEmpty *)
  (* let isString = Constr.isConstr mkString *)

  let rec from_coq env sigma s =
    let (h, args) = whd_all_stack env sigma s in
    if isEmpty sigma h then
      ""
    else if isString sigma h then
      let c, s' = List.nth args 0, List.nth args 1 in
      CoqAscii.from_coq env sigma c ^ from_coq env sigma s'
    else
      failwith "omgg"
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


open Pp
(*                                                          lol -v    *)
(* val print : Environ.env -> Evd.evar_map -> EConstr.constr -> IO () *)
let print env sigma cons = Feedback.msg_info (str (Printf.sprintf "MTACLITE: %s\n" (CoqString.from_coq env sigma cons))) ;()

let rec interpret env sigma constr =
  let red = whd_all env sigma constr in
  let hs, args = decompose_app sigma red in
  match args with
    | [f]    when eq_constr sigma hs (Lazy.force mtacPrint) ->
        print env sigma f;
        CoqUnit.mkTT
    | [a; b] when eq_constr sigma hs (Lazy.force mtacUnify) -> CoqUnit.mkTT
    | [a; b] when eq_constr sigma hs (Lazy.force mtacBind)  -> CoqUnit.mkTT
    | [a]    when eq_constr sigma hs (Lazy.force mtacRet)   -> CoqUnit.mkTT
    | _ -> coq_true
