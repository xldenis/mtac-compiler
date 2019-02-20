open Term
open Names
open Coqlib
open Reductionops

open EConstr
open Coqffi

(* the objective here is to write the interpreter for mtaclite. Afterwards I'll write the compiler *)

open Monad
open Unify

open Pp

(*                                                          lol -v    *)
(* val print : Environ.env -> Evd.evar_map -> EConstr.constr -> IO () *)
let print env sigma cons = Feedback.msg_info (str (Printf.sprintf "MTACLITE: %s\n" (CoqString.from_coq env sigma cons))) ;()

open MtacTerm

exception Omg of string

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
        let o = CoqOption.mkSome (CoqEq.mkAppEq t a b) (CoqEq.mkAppEqRefl t a) in
        Val (env, sigma, lazy o)
      else
       let o = CoqOption.mkNothing (CoqEq.mkAppEq t a b)in
        Val (env, sigma, lazy o)
    | [_; _; a; b] when eq_constr sigma hs (Lazy.force mtacBind)  ->
      interpret env sigma goal a >>= fun (env', sigma', a') ->
        let t' = mkApp(b, [| Lazy.force a'|]) in
        let o = interpret env' sigma' goal t' in
        o
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
