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

(* checks that no variable in env to the right of i (that is, smaller
   to i) depends on i. *)
let noccurn_env env sigma i =
  let rec noc n =
    if n = 1 then true
    else
      match Environ.lookup_rel (i-n+1) env with
      | LocalAssum (nm, t) -> Vars.noccurn sigma (n-1) (EConstr.of_constr t)
      | LocalDef   (nm, a, t) ->
        Vars.noccurn sigma (n-1) (EConstr.of_constr a)
        && Vars.noccurn sigma (n-1) (EConstr.of_constr t)
        && noc (n-1)
  in noc i

let name_occurn_env env n =
  let ids = Environ.fold_named_context_reverse
    (fun s decl -> match decl with
        | LocalAssum (n', _) -> Id.Set.add n' s
        | LocalDef (n', _, _) -> Id.Set.add n' s
    )
    ~init:Id.Set.empty env in (* compute set of ids in env *)
  let ids = Id.Set.remove n ids in (* remove n *)
  let ids = Environ.really_needed env ids in (* and compute closure of ids *)
  Id.Set.mem n ids (* to finally check if n is in it *)

open Term
let mysubstn sigma t n c =
  let rec substrec in_arr depth c = begin match kind sigma c with
    | Constr.Rel k    ->
        if k<=depth then c
        else if k = depth+n then
          Vars.lift depth t
        else mkRel (k+1)
    | _ -> map_with_binders sigma succ (substrec in_arr) depth c
  end in
  substrec false 0 c


let subst_evar sigma var res term =
  let rec substrec depth term = begin match kind sigma term with
    | e when eq_constr sigma (of_kind e) var -> res
    | _ -> map_with_binders sigma succ (substrec) depth term
  end in
  substrec 0 term

let abs ?(mkprod=false) (env, sigma) a p x y =
  let x = whd_all env sigma x in

    (* check if the type p does not depend of x, and that no variable
       created after x depends on it.  otherwise, we will have to
       substitute the context, which is impossible *)
  if isRel sigma x then
    let rel = destRel sigma x in
    if Vars.noccurn sigma rel p then
      if noccurn_env env sigma rel then
        try
          let y' = mysubstn sigma (mkRel 1) rel y in
          if mkprod
          then mkProd   (Names.Anonymous, a, y')
          else mkLambda (Names.Anonymous, a, y')
        with _ ->
          Loc.raise (Omg "abstract ref error??")
      else
        Loc.raise (Omg "error_abs_env")
    else
      Loc.raise (Omg "error_abs_type")
  else if isVar sigma x then
    let name = destVar sigma x in
    if not (Termops.occur_var env sigma name p) then
      if not (name_occurn_env env name) then
        let y' = Vars.subst_vars [name] y in
        if mkprod
        then mkProd   (Name name, a, y')
        else mkLambda (Name name, a, y')
      else
        Loc.raise (Omg "error_abs_env")
    else
      Loc.raise (Omg "error_abs_type")
  else
    Loc.raise (Omg "error_abs")

let clean_unused_metas sigma metas term =
  let rec rem (term : constr) (metas : Evar.Set.t) =
    let fms = Evd.evars_of_term (EConstr.Unsafe.to_constr term) in
    let (metas : Evar.Set.t) = Evar.Set.diff metas fms in
    Evar.Set.fold (fun ev metas ->
      let ev_info = Evd.find sigma ev  in
      let metas = rem (Evd.evar_concl ev_info) metas in
      let metas = List.fold_right (fun named  metas ->
        match named with
        | Context.Named.Declaration.LocalAssum (_, ty) -> rem ty metas
        | LocalDef   (_, v, ty) -> let metas = rem ty metas in rem v metas
        ) (Evd.evar_context ev_info) metas in
      match Evd.evar_body ev_info with
      | Evar_empty -> metas
      | Evar_defined b -> rem b metas
      ) fms metas
  in
  let metas = rem term metas in
  (* remove all the reminding metas *)
  Evar.Set.fold (fun ev sigma -> Evd.remove (sigma : Evd.evar_map) ev) metas sigma

(* let post_cleanup res =
  match res with
  | Val (istate, env, sigma, res) -> let
      sigma' = clean_unused_metas sigma envs
    in Val (istate, env, sigma', res)
 *)

let rec interpret istate env sigma goal constr =
  let red = whd_all env sigma constr in
  let hs, args = decompose_app sigma red in

  match args with
    | [f]    when eq_constr sigma hs (Lazy.force mtacPrint) ->
        print env sigma f;
        Val (istate, env, sigma, CoqUnit.mkTT)
    | [t; a; b] when eq_constr sigma hs (Lazy.force mtacUnify) ->
      let a_red = whd_all env sigma a in
      let b_red = whd_all env sigma b in
      let unified = unify sigma env [] a_red b_red in
      (* Feedback.msg_info (Printer.pr_econstr ( a_red)) ; *)
      (* Feedback.msg_info (Printer.pr_econstr ( b_red)) ; *)

      begin match unified with
      | (true, sigma') ->
        let o = CoqOption.mkSome (CoqEq.mkAppEq t a b) (CoqEq.mkAppEqRefl t a) in
        Val (istate, env, sigma', lazy o)
      | (false, sigma') ->
       let o = CoqOption.mkNothing (CoqEq.mkAppEq t a b) in
        Val (istate, env, sigma', lazy o)
      end
    | [_; _; a; b] when eq_constr sigma hs (Lazy.force mtacBind)  ->
      interpret istate env sigma goal a >>= fun (istate, env', sigma', a') ->
        let t' = mkApp(b, [| Lazy.force a'|]) in
        let o = interpret istate env' sigma' goal t' in
        o
    | [_; a]    when eq_constr sigma hs (Lazy.force mtacRet)  -> Val (istate, env, sigma, lazy a)
    | [_; a]    when eq_constr sigma hs (Lazy.force mtacRaise) -> Err (istate, env, sigma, lazy a)
    | [a; b; s; i; f; x] when eq_constr sigma hs (Lazy.force mtacFix) ->
        let fixf = mkApp(hs, [|a; b;s;i;f|]) in
        let c = mkApp (f, [|fixf; x|]) in
        interpret istate env sigma goal c
    | [a1; a2; b; s; i; f; x; y] when eq_constr sigma hs (Lazy.force mtacFix2) ->
        let fixf = mkApp(hs, [|a1; a2; b;s;i;f|]) in
        let c = mkApp (f, [|fixf; x; y|]) in
        interpret istate env sigma goal c

    | [a; _; f] when eq_constr sigma hs (Lazy.force mtacNu) ->
        let id  = fresh_name "nu" istate in
        let fx  = mkApp(f, [|mkVar id|]) in
        let env = push_named (Context.Named.Declaration.LocalAssum ( id, a)) env in

        begin
        match (interpret istate env sigma goal fx) with
        | Val (istate, env, sigma, co) ->
          let co' = Lazy.force co in
          (* check that our variable isn't leaked *)
          if Termops.occur_var env sigma id co' then
            Loc.raise (Omg "can't leak variables from inside nu")
          else
            Val (istate, env, sigma, lazy (Termops.pop co'))
          (* return *)
        | Err (istate, env, sigma, er) -> Err (istate, env, sigma, er)

        end
    | [a] when eq_constr sigma hs (Lazy.force mtacEvar) ->
        let (sigma', ev) = Evarutil.new_evar env sigma a in
        let Evar (k, a) = EConstr.kind sigma' ( ev) in
        Val (istate, env, sigma', lazy ev)
    | [a; m; r] when eq_constr sigma hs (Lazy.force mtacTry) ->
        begin
        match (interpret istate env sigma goal m) with
        | Val (i, a, b, c) -> Val (i, a, b, c)
        | Err(_, _, _, _) -> interpret istate env sigma goal r
        end
    | [a; p; x; y] when eq_constr sigma hs (Lazy.force mtacAbs) ->
        let v = abs (env, sigma) a p x y in

        Val (istate, env, sigma, lazy v)
    | _ -> Feedback.msg_info (str (Printf.sprintf "%d" (List.length args)));
        Val (istate, env, sigma, lazy constr)

let run env sigma goal constr =
  interpret { fresh_counter = ref 0; metas = 0} env sigma goal constr
