open Nativelambda

open Util
open Coqffi
open EConstr

(*
  This pass strips the callType calls that were previously inserted, replacing them with accumulators.

  The branch of Coq this compiled is based off on adds a specific constructor to nativelambda that enables
  us generate accumulators in the native code.
*)

let mkLapp f args =
  if Array.is_empty args then f
  else
    match f with
    | Lapp(f', args') -> Lapp (f', Array.append args' args)
    | _ -> Lapp(f, args)

let mkLlam ids body =
  if Array.is_empty ids then body
  else
    match body with
    | Llam(ids', body) -> Llam(Array.append ids ids', body)
    | _ -> Llam(ids, body)

(* mk_constant_accu turn into lval with the accu inside!?!? *)
open Names

let rec tag_to_accu env sigma (l : lambda) =
  let (mtacLazyConst, _) = destConst sigma (Lazy.force MtacTerm.mtacLazy) in
  begin match l with
  | Lapp (Lconst (p, (c, i)), args) ->
    if Names.eq_constant_key c mtacLazyConst then
      let real_func = Array.get args 1 in
      Feedback.msg_info (Pp.str "making lazy tag") ;

      let func' = begin match real_func with
                  (* | Lconst (p, c) -> Lconst_accu (p, c) *)
                  | a -> a
                  end in

      let args' = Array.map (tag_to_accu env sigma) (Array.sub args 2 (Array.length args - 2)) in
      Lapp(func', args')
    else
      let args' = Array.map (tag_to_accu env sigma) args in
      Lapp (Lconst (p, (c, i)), args')
  | otherwise -> map_lam_with_binders (fun n x -> x) (fun _ x -> tag_to_accu env sigma x) 0 otherwise
  end
