
(*
  I believe this function was useful in the full version of mtac where it was used inside the mmatch branches
  i assume the purpose was to check that we didn't leak any Evars that were introduced by deconstructingg in a branch?

  I'm not educated enough yet to figure out if it's actually necessary though...
 *)
let find_pbs (sigma : Evd.evar_map) (evars : EConstr.constr list ) : Evd.evar_constraint list =
    let (_, pbs) = Evd.extract_all_conv_pbs sigma in
    List.filter (fun (_,_,c1,c2) ->
      List.exists (fun e ->
    (Termops.dependent sigma e c1) || Termops.dependent sigma e c2) evars) pbs

(* unify : Evd.evar_map -> Environ.env -> EConstr.constr list -> Econstr -> Econstr -> bool *)
let unify sigma env evars t1 t2  : bool * Evd.evar_map =
  try
    (* it appears that the_conv_x is the way to actually run the coq unification engine *)
    let unif_sigma = Evarconv.the_conv_x env t2 t1 sigma in
    (* this apparently attempts to apply a bunch a heuristics ?  *)
    let remaining  = Evarconv.consider_remaining_unif_problems env unif_sigma in
    (List.length (find_pbs remaining evars) = 0, unif_sigma)
  with _ -> (false, sigma)
