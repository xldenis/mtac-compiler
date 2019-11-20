open Tag_calls
open Monad

let def_state = { fresh_counter = ref 0; metas = 0}

let evars_of_evar_map sigma =
  { Nativelambda.evars_val = Evd.existential_opt_value0 sigma;
    Nativelambda.evars_metas = Evd.meta_type0 sigma }


let compile env sigma goal term =
  let tagged_term = tag_calls env sigma term in
  Feedback.msg_info (Printer.pr_econstr_env env sigma tagged_term) ;
  let unsafe_tagged = EConstr.Unsafe.to_constr tagged_term in
  let unsafe_term = EConstr.Unsafe.to_constr term in
  let sigma_evars = evars_of_evar_map sigma in
  let native_lambda = Nativelambda.lambda_of_constr env sigma_evars unsafe_tagged in
  Feedback.msg_info (Lambda_printer.pp_lambda env sigma native_lambda) ;
  let native_term = Nativelambda.lambda_of_constr env sigma_evars unsafe_term in
  (* Feedback.msg_info (Lambda_printer.pp_lambda env sigma native_term) ; *)

  let accud = Tag_to_accu.tag_to_accu env sigma native_lambda in
  Feedback.msg_info (Lambda_printer.pp_lambda env sigma accud) ;
  Val (def_state, env, sigma, lazy term)


