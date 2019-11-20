open Nativelambda

open Util
open Coqffi
open EConstr

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


let map_lam_with_binders g f n lam =
  match lam with
  | Lrel _ | Lvar _  | Lconst _ | Lproj _ | Lval _ | Lsort _ | Lind _ | Luint _
  | Lconstruct _ | Llazy | Lforce | Lmeta _ -> lam
  | Lprod(dom,codom) ->
      let dom' = f n dom in
      let codom' = f n codom in
      if dom == dom' && codom == codom' then lam else Lprod(dom',codom')
  | Llam(ids,body) ->
      let body' = f (g (Array.length ids) n) body in
      if body == body' then lam else mkLlam ids body'
  | Lrec(id,body) ->
      let body' = f (g 1 n) body in
      if body == body' then lam else Lrec(id,body')
  | Llet(id,def,body) ->
      let def' = f n def in
      let body' = f (g 1 n) body in
      if body == body' && def == def' then lam else Llet(id,def',body')
  | Lapp(fct,args) ->
      let fct' = f n fct in
      let args' = Array.Smart.map (f n) args in
      if fct == fct' && args == args' then lam else mkLapp fct' args'
  | Lprim(prefix,kn,op,args) ->
      let args' = Array.Smart.map (f n) args in
      if args == args' then lam else Lprim(prefix,kn,op,args')
  | Lcase(annot,t,a,br) ->
      let t' = f n t in
      let a' = f n a in
      let on_b b =
  let (cn,ids,body) = b in
  let body' =
    if Array.is_empty ids then f n body
    else f (g (Array.length ids) n) body in
  if body == body' then b else (cn,ids,body') in
      let br' = Array.Smart.map on_b br in
      if t == t' && a == a' && br == br' then lam else Lcase(annot,t',a',br')
  | Lif(t,bt,bf) ->
      let t' = f n t in
      let bt' = f n bt in
      let bf' = f n bf in
      if t == t' && bt == bt' && bf == bf' then lam else Lif(t',bt',bf')
  | Lfix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = Array.Smart.map (f n) ltypes in
      let lbodies' = Array.Smart.map (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lfix(init,(ids,ltypes',lbodies'))
  | Lcofix(init,(ids,ltypes,lbodies)) ->
      let ltypes' = Array.Smart.map (f n) ltypes in
      let lbodies' = Array.Smart.map (f (g (Array.length ids) n)) lbodies in
      if ltypes == ltypes' && lbodies == lbodies' then lam
      else Lcofix(init,(ids,ltypes',lbodies'))
  | Lmakeblock(prefix,cn,tag,args) ->
      let args' = Array.Smart.map (f n) args in
      if args == args' then lam else Lmakeblock(prefix,cn,tag,args')
  | Levar (evk, args) ->
    let args' = Array.Smart.map (f n) args in
    if args == args' then lam else Levar (evk, args')

(* mk_constant_accu turn into lval with the accu inside!?!? *)
open Names

let rec scan_args env (sigma : Evd.evar_map) (l : lambda list) =
  begin match l with
  | Lconst (p, (c, i)) :: xs ->
    let (mtacLazyConst, _) = destConst sigma (Lazy.force MtacTerm.mtacLazy) in

    Feedback.msg_info (Printer.pr_constant env c) ;
    Feedback.msg_info (Printer.pr_constant env mtacLazyConst) ;
    if Names.eq_constant_key c mtacLazyConst then
      Obj.magic ()
    else
      Lconst (p, (c, i)) :: scan_args env sigma xs
  | o :: xs -> o :: scan_args env sigma xs
  | [] -> []
  end

let rec tag_to_accu env sigma (l : lambda) =
  let (mtacLazyConst, _) = destConst sigma (Lazy.force MtacTerm.mtacLazy) in
  begin match l with
  | Lapp (Lconst (p, (c, i)), args) ->
    if Names.eq_constant_key c mtacLazyConst then
      let real_func = Array.get args 1 in
      let func' = begin match real_func with
                  | Lconst (p, c) -> Lconst_accu (p, c)
                  | a -> a
                  end in

      Lapp(func', Array.sub args 2 (Array.length args - 2))
    else
      Lapp (Lconst (p, (c, i)), args)
  (* | Lapp (func, body) -> Lapp(func, Array.of_list (scan_args env sigma (Array.to_list body))) *)
  | otherwise -> map_lam_with_binders (fun n x -> x) (fun _ x -> tag_to_accu env sigma x) 0 otherwise
  end
