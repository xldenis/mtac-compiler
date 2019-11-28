open EConstr
open Coqffi

let monadic_type sigma (ty : constr) =
  let mnd, _ = decompose_app sigma ty in
  let mtac  = (Lazy.force MtacTerm.mtacMtac) in
  eq_constr sigma mtac mnd

(*
  This is where the magic happens!

  The idea of this pass is to traverse the tree of our tactical term and look at every function application
  and wrap every pure function call with `callType` a function defined in `MtacLite` which we use to mark
  points in the tree that should be lazy. Later in the compilation we lose access to the type information
  so it's much easier to modify the tree to mark the relevant spots ahead of time.

  ====

  Γ ⊢ f a1...an : T --> ⟦ f a1...an ⟧ --> callType(f) ⟦a1⟧...⟦an⟧ if T ≆ Mtac A and f is a constant (constructor, function)
  Γ ⊢ f a1...an : T --> ⟦ f a1...an ⟧ --> f ⟦a1⟧...⟦an⟧           if T ≅ Mtac A and f is a constant (constructor, function)
  Γ ⊢ f a1...an : T --> ⟦ f a1...an ⟧ --> ⟦ f ⟧ ⟦a1⟧...⟦an⟧        otherwise
*)
let rec tag_calls env sigma (c : constr) : constr =
  begin match kind sigma c with
  | (App (f, args)) ->
    let args' = Array.map (tag_calls env sigma) args in
    begin match kind sigma f with
    | Const constr ->
      let ty = Retyping.get_type_of env sigma c in
      if monadic_type sigma ty then
        mkApp (f, args')
      else
        let fty = Retyping.get_type_of env sigma f in
        let lazy_call = mkApp (Lazy.force MtacTerm.mtacLazy, [|fty; f|]) in
        mkApp (lazy_call, args')
    | f -> let f' = tag_calls env sigma (of_kind f) in
        mkApp (f', args')
    end
  | _ -> map_with_binders sigma (fun x -> x) (fun l c -> tag_calls env sigma c) 0 c
  end

