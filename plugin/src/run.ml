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

module CoqSumBool = struct
  let left = lazy (find_constant ["Coq"; "Init"; "Specif"] "left")
  let right = lazy (find_constant ["Coq"; "Init"; "Specif"] "right")

  let mkLeft a b l = mkApp(Lazy.force left, [|a; b; l|])

  let mkRight a b r = mkApp(Lazy.force right, [|a;b;r|])
end

module MtacTerm = struct
  let path = ["MtacLite"; "MtacLite"; "MtacLite"]

  let mtacPrint = lazy (find_constant path "print")
  let mtacBind  = lazy (find_constant path "bind" )
  let mtacRet   = lazy (find_constant path "ret"  )
  let mtacUnify = lazy (find_constant path "unify")
  let mtacFix   = lazy (find_constant path "fix"  )
  let mtacRaise = lazy (find_constant path "raise")
  let mtacNu    = lazy (find_constant path "nu"   )
  let mtacEvar  = lazy (find_constant path "evar" )
  let mtacTry   = lazy (find_constant path "try"  )
end

(* the objective here is to write the interpreter for mtaclite. Afterwards I'll write the compiler *)


(* MONADS !! :) *)
type data = Val of (Environ.env * Evd.evar_map * EConstr.constr lazy_t)
      | Err of (Environ.env * Evd.evar_map * EConstr.constr lazy_t)


let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v

(* let return s es t = Val (s, es, t)

let fail s es t = Err (s, es, t)
 *)

(*
  I believe this function was useful in the full version of mtac where it was used inside the mmatch branches
  i assume the purpose was to check that we didn't leak any Evars that were introduced by deconstructingg in a branch?

  I'm not educated enough yet to figure out if it's actually necessary though...
 *)
let find_pbs (sigma : Evd.evar_map) (evars : EConstr.constr list ) : Evd.evar_constraint list =
    let (_, pbs) = Evd.extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) ->
      List.exists (fun e ->
    (Termops.dependent sigma e (EConstr.of_constr c1)) || Termops.dependent sigma e (EConstr.of_constr c2)) evars) pbs
open Pp

(* unify : Evd.evar_map -> Environ.env -> EConstr.constr list -> Econstr -> Econstr -> bool *)
let unify sigma env evars t1 t2  : bool =
  try
    (* it appears that the_conv_x is the way to actually run the coq unification engine *)
    let unif_sigma = Evarconv.the_conv_x env t2 t1 sigma in
    (* this apparently attempts to apply a bunch a heuristics ?  *)
    let remaining  = Evarconv.consider_remaining_unif_problems env unif_sigma in
        List.length (find_pbs remaining evars) = 0
  with _ -> false

open MtacTerm

exception Omg of string

(*                                                          lol -v    *)
(* val print : Environ.env -> Evd.evar_map -> EConstr.constr -> IO () *)
let print env sigma cons = Feedback.msg_info (str (Printf.sprintf "MTACLITE: %s\n" (CoqString.from_coq env sigma cons))) ;()

let rec interpret env sigma goal constr =
  let red = whd_all env sigma constr in
  let hs, args = decompose_app sigma red in

  match args with
    | [f]    when eq_constr sigma hs (Lazy.force mtacPrint) ->
        print env sigma f;
        Val (env, sigma, CoqUnit.mkTT)
    | [t; a; b] when eq_constr sigma hs (Lazy.force mtacUnify) ->
      let a_red = whd_all env sigma a in
      let b_red = whd_all env sigma b in
      let unified = unify sigma env [] a_red b_red in
      if unified then
        let o = CoqSumBool.mkLeft (CoqEq.mkAppEq t a b) (CoqEq.mkAppNot (CoqEq.mkAppEq t a b)) ((CoqEq.mkAppEqRefl t a)) in
        Val (env, sigma, lazy o)
      else
       let o = CoqSumBool.mkRight (CoqEq.mkAppEq t a b) (CoqEq.mkAppNot (CoqEq.mkAppEq t a b)) ((CoqEq.mkAppEqRefl t a)) in
        Val (env, sigma, lazy o)
    | [_; _; a; b] when eq_constr sigma hs (Lazy.force mtacBind)  ->
      Feedback.msg_info (str "omg");
      interpret env sigma goal a >>= fun (env', sigma', a') ->
        Feedback.msg_info (str "omg-2");
        let t' = mkApp(b, [| Lazy.force a'|]) in
        let o = interpret env' sigma' goal t' in
        Feedback.msg_info (str "omg-3"); o

    | [_; a]    when eq_constr sigma hs (Lazy.force mtacRet)  -> Val (env, sigma, lazy a)
    | [_; a]    when eq_constr sigma hs (Lazy.force mtacRaise) -> Err (env, sigma, lazy a)
    | [a; b; s; i; f; x] when eq_constr sigma hs (Lazy.force mtacFix) ->
        let fix_iter = mkApp(hs, [|a; b; s; i; f; x|]) in
        let c = mkApp(f, [|fix_iter; x|]) in
        interpret env sigma goal c
    | [a; _; f] when eq_constr sigma hs (Lazy.force mtacNu) ->
        let fx  = mkApp(Vars.lift 1 f, [|mkRel 1|]) in (* wtf is mkRel? *)
        let env = push_rel (LocalAssum (Anonymous, a)) env in
        begin
        match (interpret env sigma goal fx) with
        | Val (env, sigma, co) ->
          let co' = Lazy.force co in
          (* check that our variable isn't leaked *)
          if Int.Set.mem 1 (Termops.free_rels sigma co') then
            Loc.raise (Omg "omg")
          else
            Val (env, sigma, lazy (Termops.pop co'))
          (* return *)
        | Err (env, sigma, er) ->
          (* check for variable leak *)
          (* fail *)
            Loc.raise (Omg "omg-2")
        end
    | [a] when eq_constr sigma hs (Lazy.force mtacEvar) ->
        let (sigma', ev) = Evarutil.new_evar env sigma a in
        Val (env, sigma', lazy ev)
    | [a; m; r] when eq_constr sigma hs (Lazy.force mtacTry) ->
        begin
        match (interpret env sigma goal m) with
        | Val (a, b, c) -> Val (a, b, c)
        | Err(_, _, _) -> interpret env sigma goal r
        end
    | _ -> Feedback.msg_info (str (Printf.sprintf "%d" (List.length args)));
        Val (env, sigma, lazy constr)
