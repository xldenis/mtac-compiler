open EConstr
open Coqffi

let monadic_type sigma (ty : constr) =
  let mnd, _ = decompose_app sigma ty in
  let mtac  = (Lazy.force MtacTerm.mtacMtac) in
  eq_constr sigma mtac mnd

let rec tag_calls env sigma (c : constr) : constr =
  begin match kind sigma c with
  | (App (f, args)) ->
    let args' = Array.map (tag_calls env sigma) args in
    begin match kind sigma f with
    | Const constr ->
      let ty = Retyping.get_type_of env sigma (c) in
      if monadic_type sigma ty then
        of_kind (App (of_kind (Const constr), args'))
      else
        Obj.magic ()
    | f -> let f' = tag_calls env sigma (of_kind f) in
        mkApp (f', args')
    end
  | _ -> map_with_binders sigma (fun x -> x) (fun l c -> tag_calls env sigma c) 0 c
  end

