(*
  Mtaclite Compiler

  Here we define the native compilation and interpretation of Mtaclite values.

  We need to copy all the native compilation code from Coq because the current
  api is too restrictive, notably it doesn't export the `nf_*` family of functions
  that are required to perform the readback of a native term.

 *)

open CErrors
open Term
open Constr
open Vars
open Environ
open Reduction
open Declarations
open Names
open Inductive
open Util
open Nativecode
open Nativevalues
open Context.Rel.Declaration

open Nativenorm
(* The actual code *)

open Coqffi
open Pp

let print env sigma cons = Feedback.msg_info (str (Printf.sprintf "MTACLITE: %s\n" (CoqString.from_coq env sigma cons))) ;()

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

let find_pbs (sigma : Evd.evar_map) (evars : EConstr.constr list ) : Evd.evar_constraint list =
    let (_, pbs) = Evd.extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) ->
      List.exists (fun e ->
    (Termops.dependent sigma e ( c1)) || Termops.dependent sigma e ( c2)) evars) pbs

open Monad
open Coqffi

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

let print_constr arg = Feedback.msg_info (Printer.pr_econstr (EConstr.of_constr arg))

(* Get the correct 'Type' used in Mtac *)
let type_univ_of_constr env sigma v : types =
  let mtac  = EConstr.Unsafe.to_constr(Lazy.force MtacTerm.mtacMtac) in
  let _, ctyp = construct_of_constr_block env sigma (block_tag (Obj.magic v)) mtac in
  let _, tta, _ = decompose_prod env ctyp in
  tta

(* Native interpreter
  The interpreter takes some state variables and a `Nativevalues.t` term to evaluate
  During native compilation everything is a `Nativevalues.t` and is coerced to the
  correct type when needed, which is safe because the term was originally a well typed
  Gallina term.

  Here we start by coercing it to an mtaclite term and matching on the constructor.

  Depending on which we may need to read back some arguments to their coq representation
  to perform operations (such as unification).
 *)
let rec interpret istate env sigma (v : Nativevalues.t) =
  (* Feedback.msg_info (Pp.str (str_of_mtaclite (Obj.magic v : mtaclite))) ; *)
  intrepret' istate env sigma v
and intrepret' istate env sigma v = begin match (Obj.magic v : mtaclite) with
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
    let env = push_named (Context.Named.Declaration.LocalAssum ( id, ta)) env in

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
      let np = nf_val env sigma p (mkArrow na tta) in
      let nx = nf_val env sigma x na in

      let reduced_type = Reductionops.whd_all env sigma (EConstr.of_constr (mkApp (np, [| nx |]))) in

      let tpx = nf_val env sigma px (EConstr.Unsafe.to_constr reduced_type) in

      let abs_lambda = Run.abs (env, sigma) (EConstr.of_constr na) (EConstr.of_constr np) (EConstr.of_constr nx) (EConstr.of_constr tpx) in

      let c = EConstr.Unsafe.to_constr abs_lambda in
      let ml_filename, prefix = Nativelib.get_ml_filename () in
      let code, upd = mk_norm_code (env) (evars_of_evar_map sigma) prefix c in

      begin match Nativelib.compile ml_filename (code) ~profile:false with
        | true, fn ->
          Nativelib.call_linker ~fatal:true prefix fn (Some (upd));
          Val (istate, env, sigma, !Nativelib.rt1)
        | _ -> assert false
      end
  end

(*
  Native compilation and interpretation of mtaclite terms.
 *)

open Nativelib

module StringSet = Set.Make(String)
open Library
let get_used_load_paths () =
  StringSet.elements
    (List.fold_left (fun acc m -> StringSet.add
      (Filename.dirname (library_full_filename m)) acc)
       StringSet.empty (loaded_libraries ()))

let _ = Nativelib.get_load_paths := get_used_load_paths

let compile env sigma _ constr =
  let t0 = Sys.time () in

  (* is this actually safe to do on all valid tactic terms? *)
  let c = EConstr.Unsafe.to_constr constr in

  let ctyp = Retyping.get_type_of env sigma constr in
  let ty = EConstr.Unsafe.to_constr ctyp in
  Feedback.msg_info (str "starting compilation");

  let ml_filename, prefix = Nativelib.get_ml_filename () in
  let code, upd = compile_tactic (env) ( sigma) prefix constr in

  match compile ml_filename code ~profile:false with
    | true, fn ->
      let t1 = Sys.time () in
      Feedback.msg_info (str (Format.sprintf "Compilation done in %.5f@." (t1 -. t0))) ;

      call_linker ~fatal: true prefix fn (None);

      (* interpret the compiled term, producing either an error or a value *)
      let Val (istate, env', sigma', res) = interpret ({ fresh_counter = ref 0; metas = 0}) env sigma !Nativelib.rt1 in

      let t2 = Sys.time () in
      Feedback.msg_info (str (Format.sprintf "Evaluation done in %.5f@." (t2 -. t1))) ;

      (* Readback of values is 'type-directed', it deconstructs the value's type as it builds up it's coq representation.
         We already know our return type is Mtac A, so we break it apart to get the A inside
       *)
      let _, [arg] = decompose_app ty in

      (* Sometimes our return type may not be normalized and this can pose problems for the readback *)
      let red = whd_all env arg in

      Feedback.msg_info (Printer.pr_econstr (EConstr.of_constr arg)) ;

      (* do the actual readback *)
      let (redback : constr) = nf_val env sigma res arg in

      let t3 = Sys.time () in
      Feedback.msg_info (str (Format.sprintf "Readback done in %.5f@." (t3 -. t2))) ;


      Val ({ fresh_counter = ref 0; metas = 0}, env, sigma, lazy (EConstr.of_constr (redback)))
    | _ -> assert false
