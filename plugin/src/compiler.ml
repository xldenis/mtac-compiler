open Tag_calls
open Monad

let def_state = { fresh_counter = ref 0; metas = 0}

let compile env sigma goal term =
  let tagged_term = tag_calls env sigma term in
  Feedback.msg_info (Printer.pr_econstr_env env sigma tagged_term) ;
  Val (def_state, env, sigma, lazy term)
