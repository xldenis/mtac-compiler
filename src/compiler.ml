open Tag_calls
open Monad
open Nativecode
open Coqffi
open Nativenorm
open Nativevalues
open Reductionops

let def_state = { fresh_counter = ref 0; metas = 0}

let evars_of_evar_map sigma =
  { Nativelambda.evars_val = Evd.existential_opt_value0 sigma;
    Nativelambda.evars_metas = Evd.meta_type0 sigma }


let tactic_of_constr (sigma : Evd.evar_map) env evars term =
  let tagged = tag_calls env sigma (EConstr.of_constr term) in
  let unsafe = EConstr.Unsafe.to_constr tagged in
  let native_lambda = Nativelambda.lambda_of_constr env evars unsafe in
  let accud = Tag_to_accu.tag_to_accu env sigma native_lambda in
  accud

let mk_tactic_call env sigma prefix t =
  clear_symbols ();
  clear_global_tbl ();
  let evars = evars_of_evar_map sigma in
  let gl, upds =
    let init = ([], Obj.magic empty_updates) in
    compile_deps (tactic_of_constr sigma) env evars prefix ~interactive:true init t
  in
  let code = (tactic_of_constr sigma) env evars t in
  let (gl,code) = compile_with_fv env evars None gl None code in
  let global_code = mk_norm_harness code gl in
  global_code, upds



(*
  When coq does native compilation, it creates a random module in a temporary folder. This means
  we can't actually reference the compiled version of the Mtac inductive definition. To get around
  this we exploit the fact that OCaml chooses to represent structurually isomorphic types the same way, down to the tags.
  This means we can define an identical datatype and use Obj.magic to pass from our version to coq-native's version
*)
type mtaclite =
  | Accu  of Nativevalues.t (* ??? I don't fully understand the point of this Accu constructor... *)
  | Print of Nativevalues.t
  | Ret   of Nativevalues.t * Nativevalues.t
  | Bind  of Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Unify of Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Fix   of Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Fix2  of Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Fail  of Nativevalues.t * Nativevalues.t
  | Nu    of Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Evar2 of Nativevalues.t
  | Try   of Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Abs   of Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t

type coq_unit =
  | AccuUnit of Nativevalues.t
  | CoqUnit

type coq_option =
  | AccuOption of Nativevalues.t
  | CoqSome of Nativevalues.t
  | CoqNone

type coq_eq =
  | AccuEq of Nativevalues.t
  | EqRefl

open Pp

let print env sigma cons = Feedback.msg_info (str (Printf.sprintf "MTACLITE: %s\n" (CoqString.from_coq env sigma cons))) ;()

let nf_val = Obj.magic ()
let construct_of_constr_block = Obj.magic ()

open Context
open Names
open EConstr

let decompose_prod env sigma t =
  let (name,dom,codom) = EConstr.destProd sigma (whd_all env sigma t) in
  let name = Context.map_annot (function
      | Name.Anonymous -> Name (Id.of_string "x")
      | na -> na) name
  in
  (name,dom,codom)

let str_of_mtaclite v = match v with
  | Print _ -> "print"
  | Ret _ -> "ret"
  | Bind _ -> "bind"
  | Unify _ -> "unify"
  | Fail _ -> "fail"
  | Evar2 _ -> "evar"
  | Try _ -> "try"
  | Nu _ -> "nu"
  | Fix _ -> "fix"
  | Accu _ -> "accu"

(* Get the correct 'Type' used in Mtac *)
let type_univ_of_constr env sigma v : types =
  let mtac  = EConstr.Unsafe.to_constr(Lazy.force MtacTerm.mtacMtac) in
  let _, ctyp = construct_of_constr_block env sigma (block_tag (Obj.magic v)) mtac in
  let _, tta, _ = decompose_prod env sigma ctyp in
  tta

(*
  Interpreter for monadic effects of MtacLite

  This interpreter takes a native representation of a term of type Mtac A, and performs the effect denoted by the head-constructor.
  Some effects may require a read-back of some or all the arguments in the term (unification) or may even require _compiling_ the returned value (nu)
*)

let rec interpret istate env sigma (v : Nativevalues.t) =
  Feedback.msg_info (Pp.str (str_of_mtaclite (Obj.magic v : mtaclite))) ;
  intrepret' istate env sigma v
and intrepret' istate env sigma v = begin match (Obj.magic v : mtaclite) with
  | Accu acc ->
    let strty = EConstr.Unsafe.to_constr (Lazy.force CoqString.stringTy) in
    let r = Nativelite.nf_val env sigma v strty in

    Feedback.msg_info (str "BLOCKED ON ACCU: " ++ Printer.pr_constr_env env sigma r);
    Err (istate, env, sigma, Obj.magic ())
  | Print s ->
    let strty = EConstr.Unsafe.to_constr (Lazy.force CoqString.stringTy) in
    let normed = nf_val env sigma s strty in (* i can hardcode the string type here *)
    print env sigma (EConstr.of_constr normed);
    Val (istate, env, sigma, Obj.magic CoqUnit)

  | Ret (t, f) -> Val (istate, env, sigma, f)
  | Bind (ta, tb, a, b) ->
    interpret istate env sigma a >>= fun (istate, e, s, ma) ->
      interpret istate e s ((Obj.magic b) ma)
  | Unify (ta, a, b) -> (* how do we get the type here? do.a readback of ta with type Type ?? but whicch Type?? *)
    let tta = type_univ_of_constr env sigma v in
    let nta = nf_val env sigma ta tta in
    let na = nf_val env sigma a nta in
    let nb = nf_val env sigma b nta in

      (* Feedback.msg_info (Printer.pr_constr ( na)) ; *)
      (* Feedback.msg_info (Printer.pr_constr ( nb)) ; *)

    let unified = Unify.unify sigma env [] (EConstr.of_constr na) (EConstr.of_constr nb) in

    begin match unified with
    | (true, sigma') ->   Val (istate, env, sigma', Obj.magic (CoqSome (Obj.magic EqRefl)))
    | (false, sigma') ->  Val (istate, env, sigma', Obj.magic (CoqNone))
    end
  | Fail (t, s) -> Err (istate, env, sigma, s)
  | Evar2 t ->    (* sketchy as SHIIIIIT *)
    let tta = type_univ_of_constr env sigma v in
    let nta = nf_val env sigma t tta in
    let (sigma', ev) = Evarutil.new_evar env sigma (EConstr.of_constr nta) in
    let Evar (k, a) = EConstr.kind sigma' ( ev) in

    let args = Array.map (fun var ->
      begin match (EConstr.kind sigma' var) with
      | Var id -> mk_var_accu ( id)
      | _ -> assert false
      end) a in

    let ev_accu = mk_evar_accu k args in
      Val (istate, env, sigma', ev_accu)
  | Try (t, fst, snd) -> begin match (interpret istate env sigma fst) with
    | Val (istate, env', sigma', v) -> Val (istate, env', sigma', v)
    | Err (_, _, _, _) -> interpret istate env sigma snd
    end
  | Nu (a, b, func) ->
    let tta = type_univ_of_constr env sigma v in(* this is all to extract Type... because of universe problems *)
    let ta = nf_val env sigma  a tta in

    let id  = fresh_name "nu" istate in
    let var = mk_var_accu id in
    let env = EConstr.push_named (Context.Named.Declaration.LocalAssum (Context.annotR id, ta)) env in

    interpret istate env sigma ((Obj.magic func) var)
  | Fix (a, b, s, i, f, x) ->
    let fixf = (fun x ->
      Obj.magic (Fix (a, b, s, i, f, x)) : Nativevalues.t) in
    let iter = (Obj.magic f) (Obj.magic fixf) x in

    interpret istate env sigma iter
  | Fix2 (a1, a2, b, s, i, f, x, y) ->
    let fixf = (fun x y ->
      Obj.magic (Fix2 (a1, a2, b, s, i, f, x, y)) : Nativevalues.t) in
    let iter = (Obj.magic f) (Obj.magic fixf) x y in

    interpret istate env sigma iter
  | Abs (a, p, x, px) ->
      let tta = type_univ_of_constr env sigma v in(* this is all to extract Type... because of universe problems *)
      let na = nf_val env sigma a tta in
      (* need to make a A -> Type fun !!! *)
      let np = nf_val env sigma p (mkArrow na Sorts.Relevant tta) in
      let nx = nf_val env sigma x na in

      let reduced_type = Reductionops.whd_all env sigma (mkApp (np, [| nx |])) in

      let tpx = nf_val env sigma px (EConstr.Unsafe.to_constr reduced_type) in

      let abs_lambda = Run.abs (env, sigma) (EConstr.of_constr na) (EConstr.of_constr np) (EConstr.of_constr nx) (EConstr.of_constr tpx) in

      let c = EConstr.Unsafe.to_constr abs_lambda in
      let ml_filename, prefix = Nativelib.get_ml_filename () in
      let code, upd = mk_norm_code Nativelambda.lambda_of_constr (env) (evars_of_evar_map sigma) prefix c in

      let fn = Nativelib.compile ml_filename (code) ~profile:false in
      Nativelib.call_linker ~fatal:true prefix fn (Some (upd));
      Val (istate, env, sigma, !Nativelib.rt1)
  end

(* Compiling, evaluating, reading back and returning *)
let compile env sigma _ constr =
  let t0 = Sys.time () in

  (* is this actually safe to do on all valid tactic terms? *)
  let c = EConstr.Unsafe.to_constr constr in

  let ctyp = Retyping.get_type_of env sigma constr in
  let ty = ctyp in
  Feedback.msg_info (str "starting compilation");

  let ml_filename, prefix = Nativelib.get_ml_filename () in
  let code, upd = mk_tactic_call env sigma prefix c in

  let fn = Nativelib.compile ml_filename code ~profile:false in
  let t1 = Sys.time () in
  Feedback.msg_info (str (Format.sprintf "Compilation done in %.5f@." (t1 -. t0))) ;

  Nativelib.call_linker ~fatal: true prefix fn (None);

  (* interpret the compiled term, producing either an error or a value *)
  let res = interpret ({ fresh_counter = ref 0; metas = 0}) env sigma !Nativelib.rt1 in

  let t2 = Sys.time () in
  Feedback.msg_info (str (Format.sprintf "Evaluation done in %.5f@." (t2 -. t1))) ;
  (* Readback of values is 'type-directed', it deconstructs the value's type as it builds up it's coq representation.
     We already know our return type is Mtac A, so we break it apart to get the A inside
   *)
  let _, [arg] = decompose_app sigma ty in

  (* Sometimes our return type may not be normalized and this can pose problems for the readback *)
  let red = whd_all env sigma arg in

  match res with
  | Val (istate, env', sigma', res) -> begin
    (* do the actual readback *)
    let (redback : Constr.t) = Nativenorm.nf_val env' sigma' res (EConstr.Unsafe.to_constr arg) in

    let t3 = Sys.time () in
    Feedback.msg_info (str (Format.sprintf "Readback done in %.5f@." (t3 -. t2))) ;

    Val ({ fresh_counter = ref 0; metas = 0}, env', sigma', lazy (EConstr.of_constr redback))
    end
  | Err (istate, env', sigma', res) -> begin
    Feedback.msg_info (str "Interpretation returned an error result") ;
    (* do the actual readback *)
    let strty = EConstr.Unsafe.to_constr (Lazy.force CoqString.stringTy) in
    let (redback : Constr.t) = Nativenorm.nf_val env' sigma' res strty in

    let t3 = Sys.time () in
    Feedback.msg_info (str (Format.sprintf "Readback done in %.5f@." (t3 -. t2))) ;

    Err ({ fresh_counter = ref 0; metas = 0}, env', sigma', lazy (EConstr.of_constr redback))
    end
