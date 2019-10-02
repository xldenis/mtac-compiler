(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Names
open Constr
open Declarations
open Util
open Nativevalues
open Nativelambda
open Environ
open Context

open Nativecode
[@@@ocaml.warning "-32-37"]

let map_with_accum f acc l =
  let accum = ref acc in
  let rec go l =
    match l with
    | [] -> []
    | (x :: xs) ->
      let (acc', x') = f !accum x in
      accum := acc' ; x' :: go xs
  in (!accum, go l)

(** This file defines the mllambda code generation phase of the native
compiler. mllambda represents a fragment of ML, and can easily be printed
to OCaml code. *)
open Hashset.Combine

open Pp

(** Lambda to Mllambda **)

let empty_params = [||]

let decompose_MLlam c =
  match c with
  | MLlam(ids,c) -> ids,c
  | _ -> empty_params,c

(*s Global declaration *)

(*s Compilation environment *)

type env =
    { env_rel : (mllambda * types) list; (* (MLlocal lname) list *)
      env_bound : int; (* length of env_rel *)
      (* free variables *)
      env_urel : (int * mllambda) list ref; (* list of unbound rel *)
      env_named : (Id.t * mllambda) list ref;
      env_univ : lname option;
      env_env : Environ.env;

    }

let empty_env env univ () =
  { env_rel = [];
    env_bound = 0;
    env_urel = ref [];
    env_named = ref [];
    env_univ = univ;
    env_env = env;
  }

let push_rel env id ty =
  let local = fresh_lname id.binder_name in
  local, { env with
     env_rel = (MLlocal local, ty) :: env.env_rel;
     env_bound = env.env_bound + 1
   }

let push_rels env ids =
  let lnames, env_rel =
    Array.fold_left (fun (names,env_rel) (id, ty) ->
      let local = fresh_lname id.binder_name in
      (local::names, (MLlocal local, ty)::env_rel)) ([],env.env_rel) ids in
  Array.of_list (List.rev lnames), { env with
        env_rel = env_rel;
        env_bound = env.env_bound + Array.length ids
      }

let get_rel env id i =
  if i <= env.env_bound then
    let ml, ty = List.nth env.env_rel (i-1) in
    (ml, Some ty)
  else
    let i = i - env.env_bound in
    try Int.List.assoc i !(env.env_urel), None (* why do we need to handle unbound rels? *)

    with Not_found ->
      let local = MLlocal (fresh_lname id) in
      env.env_urel := (i,local) :: !(env.env_urel);
      local, None (* why do we need to handle unbound rels? *)


let get_var env id =
  try Id.List.assoc id !(env.env_named)
  with Not_found ->
    let local = MLlocal (fresh_lname (Name id)) in
    env.env_named := (id, local)::!(env.env_named);
    local

type rlist =
  | Rnil
  | Rcons of (constructor * lname option array) list ref * LNset.t * mllambda * rlist'
and rlist' = rlist ref

let rm_params fv params =
  Array.map (fun l -> if LNset.mem l fv then Some l else None) params

let rec insert cargs body rl =
 match !rl with
 | Rnil ->
     let fv = fv_lam body in
     let (c,params) = cargs in
     let params = rm_params fv params in
     rl:= Rcons(ref [(c,params)], fv, body, ref Rnil)
 | Rcons(l,fv,body',rl) ->
     if eq_mllambda body body' then
       let (c,params) = cargs in
       let params = rm_params fv params in
       l := (c,params)::!l
     else insert cargs body rl

let rec to_list rl =
  match !rl with
  | Rnil -> []
  | Rcons(l,_,body,tl) -> (!l,body)::to_list tl

let merge_branches t =
  let newt = ref Rnil in
  Array.iter (fun (c,args,body) -> insert (c,args) body newt) t;
  Array.of_list (to_list newt)

open Coqffi


open Pp
open Names
module RelDecl = Context.Rel.Declaration

(* Symbolic compilation of a `lambda`, turns globals into accumulators *)
let rec symbolize_lam (env : env) l t =
  match t with
  | Levar(evk, args) ->
      let i = push_symbol (SymbEvar evk) in
      (** Arguments are *not* reversed in evar instances in native compilation *)
      let args = MLarray(Array.map (symbolize_lam env l) args) in
        MLapp(MLprimitive Mk_evar, [|get_evar_code i; args|])
  | Lprod(dom,codom) ->
      let dom = symbolize_lam env l dom in
      let codom = symbolize_lam env l codom in
      let n = get_prod_name codom in
      let i = push_symbol (SymbName n) in
      MLapp(MLprimitive Mk_prod, [|get_name_code i;dom;codom|])
  | Llam(ids,body) ->
      let lnames,env = push_rels env (ids) in
      MLlam(lnames, symbolize_lam env l body)
  | Llet(id,ty, def,body) ->
      let def = symbolize_lam env l def in
      let lname, env = push_rel env id ty in
      let body = symbolize_lam env l body in
      MLlet(lname,def,body)
  | Lapp(f,args) ->
      MLapp(symbolize_lam env l f, Array.map (symbolize_lam env l) args)
  | Lprim _ ->
      let decl,cond,paux = extract_prim (symbolize_lam env l) t in
      compile_prim decl cond paux
  | Lcase (annot,p,a,bs) ->
      let env_p = empty_env env.env_env env.env_univ () in
      let pn = fresh_gpred l in
      let mlp = symbolize_lam env_p l p in
      let mlp = generalize_fv (Obj.magic env_p) mlp in
      let (pfvn,pfvr) = !(env_p.env_named), !(env_p.env_urel) in
      let pn = push_global_let pn mlp in
      (* Compilation of the case *)
      let env_c = empty_env env.env_env env.env_univ () in
      let a_uid = fresh_lname Anonymous in
      let la_uid = MLlocal a_uid in
      (* compilation of branches *)
      let ml_br (c,params, body) =
        let lnames, env_c = push_rels env_c params in
        (c, lnames, symbolize_lam env_c l body)
      in
      let bs = Array.map ml_br bs in
      let cn = fresh_gcase l in
      (* Compilation of accu branch *)
      let pred = MLapp(MLglobal pn, fv_args (Obj.magic env_c) pfvn pfvr) in
      let (fvn, fvr) = !(env_c.env_named), !(env_c.env_urel) in
      let cn_fv = mkMLapp (MLglobal cn) (fv_args (Obj.magic env_c) fvn fvr) in
         (* remark : the call to fv_args does not add free variables in env_c *)
      let i = push_symbol (SymbMatch annot) in
      let accu =
        MLapp(MLprimitive Mk_sw,
              [| get_match_code i; MLapp (MLprimitive Cast_accu, [|la_uid|]);
           pred;
           cn_fv |]) in
      let cn = push_global_case cn (Array.append (fv_params (Obj.magic env_c)) [|a_uid|])
        annot la_uid accu (merge_branches bs)
      in
      (* Final result *)
      let arg = symbolize_lam env l a in
      let force =
        if annot.asw_finite then arg
              else mkForceCofix annot.asw_prefix annot.asw_ind arg in
      mkMLapp (MLapp (MLglobal cn, fv_args (Obj.magic env) fvn fvr)) [|force|]
  | Lif(t,bt,bf) ->
      MLif(symbolize_lam env l t, symbolize_lam env l bt, symbolize_lam env l bf)

  | Lfix ((rec_pos, inds, start), (ids, tt, tb)) -> anomaly (Pp.str "Lfix")
  | Lcofix (start, (ids, tt, tb)) -> anomaly (Pp.str "Lcofix")
  | Lmakeblock (prefix,(cn,u),_, _,args) ->
      let args = Array.map (symbolize_lam env l) args in
      MLconstruct(prefix,cn,args)
  | Lconst (prefix, (cn,u)) ->
      let i = push_symbol (SymbConst cn) in

      let args = [| get_const_code i; MLarray [||] |] in
        (mkMLapp (MLprimitive (Mk_const)) args)
  | Lrel(id ,i) -> fst (get_rel env (RelDecl.get_name id) i)
  | Lvar id -> get_var env id
  | Lval (_, v) ->
      let i = push_symbol (SymbValue v) in get_value_code i
  | Lsort s ->
    let i = push_symbol (SymbSort s) in
    let uarg = match env.env_univ with
      | None -> MLarray [||]
      | Some u -> MLlocal u
    in
    let uarg = MLapp(MLprimitive MLmagic, [|uarg|]) in
    MLapp(MLprimitive Mk_sort, [|get_sort_code i; uarg|])
(*   | Lval _ -> anomaly (Pp.str "Lval")
  | Lsort _ -> anomaly (Pp.str "Lsort")
 *)  | Llazy _ -> anomaly (Pp.str "Llazy")
  | Lforce _ -> anomaly (Pp.str "Lforce")
  | Lmeta _ -> anomaly (Pp.str "Lmeta")
  | Lproj _ -> anomaly (Pp.str "Lproj")
  | Lconstruct _ -> anomaly (Pp.str "Lconstruct")
  | Luint _ -> anomaly (Pp.str "Luint")
  | Lind (prefix, (ind, u)) ->
       let uargs = ml_of_instance env.env_univ u in
       mkMLapp (MLglobal (Gind (prefix, ind))) uargs

(* Check if a type is of the form `Mtac A` *)
let monadic_type ty =
  let mnd, _ = decompose_app ty in
  let mtac  = EConstr.Unsafe.to_constr(Lazy.force MtacTerm.mtacMtac) in
  Constr.equal mtac mnd

let tactic_type ty =
  let (_, res) = Term.decompose_prod ty in
  let mnd, _ = decompose_app res in
  let mtac  = EConstr.Unsafe.to_constr(Lazy.force MtacTerm.mtacMtac) in
  Constr.equal mtac mnd

let rec ml_of_lam (env : env) l t =
  begin match t with
    | Lrel(id ,i) ->
        fst (get_rel env (RelDecl.get_name id) i), (RelDecl.get_type id)
    | Lvar _ -> anomaly (Pp.str "Lvar")
    | Lmeta _ -> anomaly (Pp.str "Lmeta")
    | Levar _ -> anomaly (Pp.str "Levar")
    | Lprod(dom,codom) ->
      let (dom, dom_ty) = ml_of_lam env l dom in
      let (codom, codom_ty) = ml_of_lam env l codom in
      let n = get_prod_name codom in
      let i = push_symbol (SymbName n) in
      MLapp(MLprimitive Mk_prod, [|get_name_code i;dom;codom|]), (mkProd (make_annot n Sorts.Relevant, dom_ty, codom_ty))
    | Llam(ids, body) ->
        let lnames,env = push_rels env (ids) in
        let (body', bty) = ml_of_lam env l body in
        let ty = Array.fold_right (fun (id, ty) acc -> mkProd (anonR, ty, acc)) ids bty in
        MLlam(lnames, body'), ty
    | Llet(id, ty, def,body) ->
      let (def, _) = ml_of_lam env l def in
      let lname, env = push_rel env id ty in
      let (body, ty) = ml_of_lam env l body in
      MLlet(lname,def,body), ty
    | Lapp (f, args) ->
      let (comp_f, f_ty) = ml_of_lam env l f in
      let (arg_tys, ret_ty) = Term.decompose_prod_n_assum (Array.length args) f_ty in
      let arg_tys = List.map Context.Rel.Declaration.get_type arg_tys in
      let (paired : (lambda * types) list ) = List.combine (Array.to_list args) (List.rev arg_tys) in
      let func_is_tactic = monadic_type ret_ty in
      let comp_arg = List.map (fun (arg, ty) ->
        if func_is_tactic && not (tactic_type ty)
        then begin
          (* Feedback.msg_info (Pp.str "symbolize app"); *)
          symbolize_lam env None arg
        end
        else begin
          let (x, _) = ml_of_lam env None arg in x
        end
      ) paired in
      MLapp(comp_f, Array.of_list comp_arg), ret_ty
    | Lmakeblock (prefix,(cn,u),cty, _,args) ->
        let ind = inductive_of_constructor cn in
        let indspec = Inductive.lookup_mind_specif env.env_env ind in
        let cons_ty = Inductive.type_of_constructor (cn, u) indspec in
        let func_is_tactic = monadic_type cty in
        let (arg_tys, ret_ty) = Term.decompose_prod cons_ty in
        let arg_tys = Array.of_list (List.rev arg_tys) in
        let diff = Array.length arg_tys - Array.length args in

        let arg_tys = Array.init (Array.length args) (fun i -> arg_tys.(diff + i)) in
        let args = Array.map2 (fun arg ty ->
          let ty = snd ty in

          if func_is_tactic && not (tactic_type ty)
          then begin
            symbolize_lam env None arg
          end
          else begin
            let (x, _) = ml_of_lam env None arg in x
          end
        ) (args) (arg_tys) in

        (* let args = (Array.map (ml_of_lam env l) args) in *)
        (* let args = (Array.map fst args) in *)
        MLconstruct(prefix,cn, args), cty
    | Lconst (prefix, (cn,u)) ->
      let args = ml_of_instance env.env_univ u in
      let (const_ty, _) = constant_type env.env_env (cn, u) in
(*       Feedback.msg_info (Printer.pr_constr const_ty);
      Feedback.msg_info (Printer.pr_constr (mkConst cn));
 *)
      mkMLapp (MLglobal(Gconstant (prefix, cn))) args, const_ty
    | Lproj _ -> anomaly (Pp.str "Lproj")
    | Lprim _ -> anomaly (Pp.str "Lprim")
    | Lcase (annot,p,a,bs) ->
      let env_p = empty_env env.env_env env.env_univ () in
      let pn = fresh_gpred l in
      let (mlp, _) = ml_of_lam env_p l p in
      let mlp = generalize_fv (Obj.magic env_p) mlp in
      let (pfvn,pfvr) = !(env_p.env_named), !(env_p.env_urel) in
      let pn = push_global_let pn mlp in
      (* Compilation of the case *)
      let env_c = empty_env env.env_env env.env_univ () in
      let a_uid = fresh_lname Anonymous in
      let la_uid = MLlocal a_uid in
      (* compilation of branches *)
      let ml_br (c,params, body) =
        let lnames, env_c = push_rels env_c params in
        (c, lnames, (ml_of_lam env_c l body))
      in
      let bs = Array.map ml_br bs in
      let b_ty = (fun (_, _, (_, t)) -> t) bs.(0) in
      let bs = Array.map (fun (a, b,(c, _)) ->(a,b,c)) bs in
      let cn = fresh_gcase l in
      (* Compilation of accu branch *)
      let pred = MLapp(MLglobal pn, fv_args (Obj.magic env_c) pfvn pfvr) in
      let (fvn, fvr) = !(env_c.env_named), !(env_c.env_urel) in
      let cn_fv = mkMLapp (MLglobal cn) (fv_args (Obj.magic env_c) fvn fvr) in
         (* remark : the call to fv_args does not add free variables in env_c *)
      let i = push_symbol (SymbMatch annot) in
      let accu =
        MLapp(MLprimitive Mk_sw,
              [| get_match_code i; MLapp (MLprimitive Cast_accu, [|la_uid|]);
           pred;
           cn_fv |]) in
      let cn = push_global_case cn (Array.append (fv_params (Obj.magic env_c)) [|a_uid|])
        annot la_uid accu (merge_branches bs)
      in
      (* Final result *)
      let (arg, _) = ml_of_lam env l a in
      let force =
        if annot.asw_finite
        then arg
        else mkForceCofix annot.asw_prefix annot.asw_ind arg in
      mkMLapp (MLapp (MLglobal cn, fv_args (Obj.magic env) fvn fvr)) [|force|], b_ty
    | Lif _ -> anomaly (Pp.str "Lif")
    | Lfix ((rec_pos, inds, start), (ids, tt, tb)) ->
      (* Compilation of type *)
      let t_norm_ty = Array.map snd ids in

      let env_t = empty_env env.env_env env.env_univ () in
      let ml_t = Array.map fst (Array.map (ml_of_lam env_t l) tt) in
      let params_t = fv_params (Obj.magic env_t) in
      let args_t = fv_args (Obj.magic env) !(env_t.env_named) !(env_t.env_urel) in
      let gft = fresh_gfixtype l in
      let gft = push_global_fixtype gft params_t ml_t in
      let mk_type = MLapp(MLglobal gft, args_t) in

      (* Compilation of norm_i *)
      let ndef = Array.length ids in
      let lf,env_n = push_rels (empty_env env.env_env env.env_univ ()) ids in
      let t_params = Array.make ndef [||] in
      let t_norm_f = Array.make ndef (Gnorm (l,-1)) in
      let mk_let envi (id,def) t = MLlet (id,def,t) in
      let mk_lam_or_let (params,lets,env) ((id, ty),def) =
        let ln,env' = push_rel env id ty in
        match def with
        | None -> (ln::params,lets,env')

        | Some lam ->
          let (lam', _) = ml_of_lam env l lam in
          (params, (ln, lam')::lets,env')
      in
      let ml_of_fix i body =
        let varsi, bodyi = decompose_Llam_Llet body in
        let paramsi,letsi,envi =
          Array.fold_left mk_lam_or_let ([],[],env_n) varsi
        in
        let paramsi,letsi =
          Array.of_list (List.rev paramsi), Array.of_list (List.rev letsi)
        in
        t_norm_f.(i) <- fresh_gnorm l;

        let (bodyi, bodyty) = ml_of_lam envi l bodyi in
        t_norm_ty.(i) <- bodyty;
        t_params.(i) <- paramsi;
        let bodyi = Array.fold_right (mk_let envi) letsi bodyi in
        mkMLlam paramsi bodyi
      in
      let tnorm = Array.mapi ml_of_fix tb in
      let fvn,fvr = !(env_n.env_named), !(env_n.env_urel) in
      let fv_params = fv_params (Obj.magic env_n) in
      let fv_args' = Array.map (fun id -> MLlocal id) fv_params in
      let norm_params = Array.append fv_params lf in
      let t_norm_f = Array.mapi (fun i body ->
        push_global_let (t_norm_f.(i)) (mkMLlam norm_params body)) tnorm in
      let norm = fresh_gnormtbl l in
      let norm = push_global_norm norm fv_params
         (Array.map (fun g -> mkMLapp (MLglobal g) fv_args') t_norm_f) in
      (* Compilation of fix *)
      let fv_args = fv_args (Obj.magic env) fvn fvr in
      let lf, env = push_rels env ids in
      let lf_args = Array.map (fun id -> MLlocal id) lf in
      let mk_norm = MLapp(MLglobal norm, fv_args) in
      let mkrec i lname =
        let paramsi = t_params.(i) in
        let reci = MLlocal (paramsi.(rec_pos.(i))) in
        let pargsi = Array.map (fun id -> MLlocal id) paramsi in
        let (prefix, ind) = inds.(i) in
        let body =
          MLif(MLisaccu (prefix, ind, reci),
            mkMLapp
              (MLapp(MLprimitive (Mk_fix(rec_pos,i)), [|mk_type; mk_norm|]))
              pargsi,
            MLapp(MLglobal t_norm_f.(i),
            Array.concat [fv_args;lf_args;pargsi]))
        in
        (lname, paramsi, body)
      in
      MLletrec(Array.mapi mkrec lf, lf_args.(start)), t_norm_ty.(start)
    | Lcofix _ -> anomaly (Pp.str "Lcofix")
    | Lconstruct (prefix, (cn,u)) ->
      let ind = inductive_of_constructor cn in
      let indspec = Inductive.lookup_mind_specif env.env_env ind in
      let cons_ty = Inductive.type_of_constructor (cn, u) indspec in

      let uargs = ml_of_instance env.env_univ u in
      mkMLapp (MLglobal (Gconstruct (prefix, cn))) uargs, cons_ty
    | Luint _ -> anomaly (Pp.str "Luint")
    | Lval (ty, v) ->
      let i = push_symbol (SymbValue v) in
      get_value_code i, ty

    | Lsort s ->
      let i = push_symbol (SymbSort s) in
      let uarg = match env.env_univ with
        | None -> MLarray [||]
        | Some u -> MLlocal u
      in
      let uarg = MLapp(MLprimitive MLmagic, [|uarg|]) in
      MLapp(MLprimitive Mk_sort, [|get_sort_code i; uarg|]), mkSort s
    | Lind (prefix, (ind, u)) ->
        let uargs = ml_of_instance env.env_univ u in
        let ind_specif = Inductive.lookup_mind_specif env.env_env ind in
        let ty = Inductive.type_of_inductive env.env_env (ind_specif, u) in

        mkMLapp (MLglobal (Gind (prefix, ind))) uargs, ty
    | Llazy -> anomaly (Pp.str "Llazy")
    | Lforce -> anomaly (Pp.str "Lforce")
  end


(*
  Compile a clambda into mllambda, after which the only work left to do
  is pretty printing the result and feeding it to the ocaml compiler
 *)
let mllambda_of_lambda env univ auxdefs l t =
  let env = empty_env env univ () in
  global_stack := auxdefs;
  let (ml, _) = ml_of_lam env l t in
  let fv_rel = !(env.env_urel) in
  let fv_named = !(env.env_named) in
  (* build the free variables *)
  let get_lname (_,t) =
   match t with
   | MLlocal x -> x
   | _ -> assert false in
  let params =
    List.append (List.map get_lname fv_rel) (List.map get_lname fv_named) in
  if List.is_empty params then
    (!global_stack, ([],[]), ml)
  (* final result : global list, fv, ml *)
  else
    (!global_stack, (fv_named, fv_rel), mkMLlam (Array.of_list params) ml)

(** Code optimization **)

(** Printing to ocaml **)

(** Compilation of elements in environment

    compile_with_fv performs 'eta-expansion' and constructs an application
    for all the free variables inside a compiled term

**)
let rec compile_with_fv env sigma univ auxdefs l t =
  let (auxdefs,(fv_named,fv_rel),ml) = mllambda_of_lambda env univ auxdefs l t in
  if List.is_empty fv_named && List.is_empty fv_rel then (auxdefs,ml)
  else apply_fv env sigma univ (fv_named,fv_rel) auxdefs ml

and apply_fv env sigma univ (fv_named,fv_rel) auxdefs ml =
  let get_rel_val (n,_) auxdefs =
    (*
    match !(lookup_rel_native_val n env) with
    | NVKnone ->
    *)
        compile_rel env sigma univ auxdefs n
(*    | NVKvalue (v,d) -> assert false *)
  in
  let get_named_val (id,_) auxdefs =
    (*
    match !(lookup_named_native_val id env) with
    | NVKnone ->
        *)
        compile_named env sigma univ auxdefs id
(*    | NVKvalue (v,d) -> assert false *)
  in
  let auxdefs = List.fold_right get_rel_val fv_rel auxdefs in
  let auxdefs = List.fold_right get_named_val fv_named auxdefs in
  let lvl = Context.Rel.length (rel_context env) in
  let fv_rel = List.map (fun (n,_) -> MLglobal (Grel (lvl-n))) fv_rel in
  let fv_named = List.map (fun (id,_) -> MLglobal (Gnamed id)) fv_named in
  let aux_name = fresh_lname Anonymous in
  auxdefs, MLlet(aux_name, ml, mkMLapp (MLlocal aux_name) (Array.of_list (fv_rel@fv_named)))

and compile_rel env sigma univ auxdefs n =
  let open Context.Rel.Declaration in
  let decl = lookup_rel n env in
  let n = List.length (rel_context env) - n in
  match decl with
  | LocalDef (_,t,_) ->
      let code = lambda_of_constr env sigma t in
      let auxdefs,code = compile_with_fv env sigma univ auxdefs None code in
      Glet(Grel n, code)::auxdefs
  | LocalAssum _ ->
      Glet(Grel n, MLprimitive (Mk_rel n))::auxdefs

and compile_named env sigma univ auxdefs id =
  let open Context.Named.Declaration in
  match lookup_named id env with
  | LocalDef (_,t,_) ->
      let code = lambda_of_constr env sigma t in
      let auxdefs,code = compile_with_fv env sigma univ auxdefs None code in
      Glet(Gnamed id, code)::auxdefs
  | LocalAssum _ ->
      Glet(Gnamed id, MLprimitive (Mk_var id))::auxdefs

let compile_constant env sigma prefix ~interactive con cb =
    let no_univs = 0 = Univ.AUContext.size (Declareops.constant_polymorphic_context cb) in
    begin match cb.const_body with
    | Def t ->
      let t = Mod_subst.force_constr t in
      let code = lambda_of_constr env sigma t in
      if !Flags.debug then Feedback.msg_debug (Pp.str "Generated lambda code");
      let is_lazy = is_lazy t in
      let code = if is_lazy then mk_lazy code else code in
      let name =
        if interactive then LinkedInteractive prefix
        else Linked prefix
      in
      let l = Constant.label con in
      let auxdefs,code =
  if no_univs then compile_with_fv env sigma None [] (Some l) code
  else
    let univ = fresh_univ () in
    let (auxdefs,code) = compile_with_fv env sigma (Some univ) [] (Some l) code in
          (auxdefs,mkMLlam [|univ|] code)
      in
      if !Flags.debug then Feedback.msg_debug (Pp.str "Generated mllambda code");
      let code =
        optimize_stk (Glet(Gconstant ("", con),code)::auxdefs)
      in
      if !Flags.debug then Feedback.msg_debug (Pp.str "Optimized mllambda code");
      code, name
    | _ ->
        let i = push_symbol (SymbConst con) in
  let args =
    if no_univs then [|get_const_code i; MLarray [||]|]
    else [|get_const_code i|]
  in
  (*
  let t = mkMLlam [|univ|] (mkMLapp (MLprimitive Mk_const)
   *)
        [Glet(Gconstant ("", con), mkMLapp (MLprimitive Mk_const) args)],
    if interactive then LinkedInteractive prefix
    else Linked prefix
    end

module StringOrd = struct type t = string let compare = String.compare end
module StringSet = Set.Make(StringOrd)

let loaded_native_files = ref StringSet.empty

let is_loaded_native_file s = StringSet.mem s !loaded_native_files

let register_native_file s =
  loaded_native_files := StringSet.add s !loaded_native_files

let is_code_loaded ~interactive name =
  match !name with
  | NotLinked -> false
  | LinkedInteractive s ->
      if (interactive && is_loaded_native_file s) then true
      else (name := NotLinked; false)
  | Linked s ->
      if is_loaded_native_file s then true
      else (name := NotLinked; false)

let param_name = Name (Id.of_string "params")
let arg_name = Name (Id.of_string "arg")


type code_location_update =
    link_info ref * link_info
type code_location_updates =
  code_location_update Mindmap_env.t * code_location_update Cmap_env.t

type linkable_code = global list * code_location_updates

let empty_updates = Mindmap_env.empty, Cmap_env.empty

(* This function compiles all necessary dependencies of t, and generates code in
   reverse order, as well as linking information updates *)
let compile_deps env sigma prefix ~interactive init t =
  let rec aux env lvl init t =
  match kind t with
  | Ind ((mind,_),u) -> compile_mind_deps env prefix ~interactive init mind
  | Const c ->
    let c,u = get_alias env c in
    let cb,(nameref,_) = lookup_constant_key c env in
    let (_, (_, const_updates)) = init in
    if is_code_loaded ~interactive nameref
    || (Cmap_env.mem c const_updates)
    then init
    else
      let comp_stack, (mind_updates, const_updates) =
        match cb.const_body with
        | Def t ->
           aux env lvl init (Mod_subst.force_constr t)
        | _ -> init
      in
      let code, name = compile_constant env sigma prefix ~interactive c cb in
      let comp_stack = code@comp_stack in
      let const_updates = Cmap_env.add c (nameref, name) const_updates in
      comp_stack, (mind_updates, const_updates)
  | Construct (((mind,_),_),u) -> compile_mind_deps env prefix ~interactive init mind
  | Proj (p,c) ->
    let init = compile_mind_deps env prefix ~interactive init (Projection.mind p) in
    aux env lvl init c
  | Case (ci, p, c, ac) ->
      let mind = fst ci.ci_ind in
      let init = compile_mind_deps env prefix ~interactive init mind in
      fold_constr_with_binders succ (aux env) lvl init t
  | Var id ->
    let open Context.Named.Declaration in
    begin match lookup_named id env with
      | LocalDef (_,t,_) ->
        aux env lvl init t
      | _ -> init
    end
  | Rel n when n > lvl ->
    let open Context.Rel.Declaration in
    let decl = lookup_rel n env in
    let env = env_of_rel n env in
    begin match decl with
    | LocalDef (_,t,_) ->
      aux env lvl init t
    | LocalAssum _ -> init
    end
  | _ -> fold_constr_with_binders succ (aux env) lvl init t
  in
  aux env 0 init t

let compile_constant_field env prefix con acc cb =
    let (gl, _) =
      compile_constant ~interactive:false env empty_evars prefix
        con cb
    in
    gl@acc

let mk_open s = Gopen s

let mk_internal_let s code =
  Glet(Ginternal s, code)

(*
  Native compilation first uses the bytecode compiler to simplify
  Gallina terms into a clambda. This representation is then lowered into
  mllambda from which we can generate the final ocaml code

 *)

(* ML Code for conversion function *)
let mk_conv_code env sigma prefix t1 t2 =
  clear_symbols ();
  clear_global_tbl ();
  let gl, (mind_updates, const_updates) =
    let init = ([], empty_updates) in
    compile_deps env sigma prefix ~interactive:true init t1
  in
  let gl, (mind_updates, const_updates) =
    let init = (gl, (mind_updates, const_updates)) in
    compile_deps env sigma prefix ~interactive:true init t2
  in
  let code1 = lambda_of_constr env sigma t1 in
  let code2 = lambda_of_constr env sigma t2 in
  let (gl,code1) = compile_with_fv env sigma None gl None code1 in
  let (gl,code2) = compile_with_fv env sigma None gl None code2 in
  let t1 = mk_internal_let "t1" code1 in
  let t2 = mk_internal_let "t2" code2 in
  let g1 = MLglobal (Ginternal "t1") in
  let g2 = MLglobal (Ginternal "t2") in
  let setref1 = Glet(Ginternal "_", MLsetref("rt1",g1)) in
  let setref2 = Glet(Ginternal "_", MLsetref("rt2",g2)) in
  let gl = List.rev (setref2 :: setref1 :: t2 :: t1 :: gl) in
  let header = Glet(Ginternal "symbols_tbl",
    MLapp (MLglobal (Ginternal "get_symbols"),
      [|MLglobal (Ginternal "()")|])) in
  header::gl, (mind_updates, const_updates)

let mk_norm_code env sigma prefix t =
  clear_symbols ();
  clear_global_tbl ();
  let gl, (mind_updates, const_updates) =
    let init = ([], empty_updates) in
    compile_deps env sigma prefix ~interactive:true init t
  in

  let code = lambda_of_constr env sigma t in
  let (gl,code) = compile_with_fv env sigma None gl None code in
  Feedback.msg_debug (Pp.int (List.length gl)) ;
  let t1 = mk_internal_let "t1" code in
  let g1 = MLglobal (Ginternal "t1") in
  let setref = Glet(Ginternal "_", MLsetref("rt1",g1)) in
  let gl = List.rev (setref :: t1 :: gl) in
  let header = Glet(Ginternal "symbols_tbl",
    MLapp (MLglobal (Ginternal "get_symbols"),
      [|MLglobal (Ginternal "()")|])) in
  header::gl, (mind_updates, const_updates)

open Coqffi

(* handle free variables in pure args!!! *)
let compile_tactic_pure_arg env sigma gl t =
  let code = Nativelambda.lambda_of_constr env sigma t in
  let env  = empty_env env None () in
  let code = symbolize_lam env None code in
  (gl, code)

let compile_tactic_monad_arg env sigma gl t =
  let code = Nativelambda.lambda_of_constr env sigma t in
  compile_with_fv env sigma None gl None code

(*
let decompose_prod t =
  let (name,dom,codom as res) = destProd t in
  match name.binder_name with
  | Anonymous -> (Name (Id.of_string "x"),dom,codom)
  | _ -> res *)

let evars_of_evar_map sigma =
  { Nativelambda.evars_val = Evd.existential_opt_value0 sigma;
    Nativelambda.evars_metas = Evd.meta_type0 sigma }

let compile_tactic env (sigma : Evd.evar_map) prefix (constr : EConstr.t) =
  (* check that result of tactic application is mtac b *)
  (* unfold application *)
  let sigma_evars = evars_of_evar_map sigma in
  let constr' = EConstr.Unsafe.to_constr constr in
  clear_symbols ();
  clear_global_tbl ();

  let gl, (mind_updates, const_updates) =
    let init = ([], empty_updates) in
    compile_deps env sigma_evars prefix ~interactive:true init constr'
  in

  let full_ty = Retyping.get_type_of env sigma constr in
  if monadic_type (EConstr.Unsafe.to_constr full_ty)
  then ()
  else anomaly (Pp.str "not a tactic type!") ;

  let header = Glet(Ginternal "symbols_tbl",
    MLapp (MLglobal (Ginternal "get_symbols"),
      [|MLglobal (Ginternal "()")|])) in

  (* let env' = empty_env env None () in *)
  let code = lambda_of_constr env sigma_evars constr' in
  let (gl,code) = compile_with_fv env sigma_evars None gl None code in

  let t1 = mk_internal_let "t1" (code) in
  let g1 = MLglobal (Ginternal "t1") in
  let (setref : global) = Glet(Ginternal "_", MLsetref("rt1", g1)) in
  let globals = List.rev (setref :: t1 :: gl) in

  (header :: globals, (mind_updates, const_updates))


let mk_library_header dir =
  let libname = Format.sprintf "(str_decode \"%s\")" (str_encode dir) in
  [Glet(Ginternal "symbols_tbl",
    MLapp (MLglobal (Ginternal "get_library_native_symbols"),
    [|MLglobal (Ginternal libname)|]))]

let update_location (r,v) = r := v

let update_locations (ind_updates,const_updates) =
  Mindmap_env.iter (fun _ -> update_location) ind_updates;
  Cmap_env.iter (fun _ -> update_location) const_updates

let add_header_comment mlcode s =
  Gcomment s :: mlcode

(* vim: set filetype=ocaml foldmethod=marker: *)
