open EConstr
open Reductionops

let find_constant dir s = EConstr.of_constr (
  UnivGen.constr_of_global (Coqlib.find_reference "mtac_plugin" dir s)
)

module CoqUnit = struct
  let mkTT : constr lazy_t = lazy (find_constant ["Coq"; "Init"; "Datatypes"] "tt")
end

module CoqBool = struct
  let mkTrue =  lazy (find_constant ["Coq"; "Init" ; "Datatypes"] "true")
  let mkFalse = lazy (find_constant ["Coq"; "Init" ; "Datatypes"] "false")

  let isTrue sigma o = eq_constr sigma (Lazy.force mkTrue) o
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
  let stringTy = lazy (find_constant ["Coq"; "Strings"; "String"] "string")

  let mkEmpty =  lazy (find_constant  ["Coq"; "Strings" ; "String"] "EmptyString")
  let mkString = lazy (find_constant ["Coq"; "Strings" ; "String"] "String")

  let isEmpty sigma o  = eq_constr sigma (Lazy.force mkEmpty) o
  let isString sigma o = eq_constr sigma (Lazy.force mkString) o

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

module CoqEq = struct
  let mkEq = lazy (find_constant ["Coq"; "Init"; "Logic"] "eq")
  let mkEqRefl = lazy (find_constant ["Coq"; "Init"; "Logic"] "eq_refl")

  let mkNot = lazy (find_constant ["Coq"; "Init"; "Logic"] "not")

  let mkAppNot x = mkApp(Lazy.force mkNot, [|x|])
  let mkAppEq a x y = mkApp(Lazy.force mkEq, [|a;x;y|])
  let mkAppEqRefl a x = mkApp(Lazy.force mkEqRefl, [|a;x|])
end

module CoqOption = struct
  let some = lazy (find_constant ["Coq"; "Init"; "Datatypes"] "Some")
  let nothing = lazy (find_constant ["Coq"; "Init"; "Datatypes"] "None")

  let mkSome a b = mkApp(Lazy.force some, [|a; b|])

  let mkNothing a  = mkApp(Lazy.force nothing, [|a|])
end

module MtacTerm = struct
  let path = ["MtacLite"; "MtacLite"; "MtacLite"]

  let mtacPrint = lazy (find_constant path "print")
  let mtacBind  = lazy (find_constant path "bind" )
  let mtacRet   = lazy (find_constant path "ret"  )
  let mtacUnify = lazy (find_constant path "unify")
  let mtacFix   = lazy (find_constant path "fix'" )
  let mtacFix2  = lazy (find_constant path "fix2'")
  let mtacRaise = lazy (find_constant path "fail" )
  let mtacNu    = lazy (find_constant path "nu"   )
  let mtacEvar  = lazy (find_constant path "evar" )
  let mtacTry   = lazy (find_constant path "try"  )
  let mtacAbs   = lazy (find_constant path "abs"  )

  let mtacMtac  = lazy (find_constant path "Mtac" )
  let mtacLazy = lazy (find_constant path "callType")
end
