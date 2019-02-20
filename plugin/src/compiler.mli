open Monad
open EConstr

val compile :
  Environ.env ->
  Evd.evar_map ->
  'a ->
  constr ->
  (constr lazy_t) data

val construct_of_constr : bool -> Environ.env -> Evd.evar_map -> int -> Retroknowledge.entry -> Retroknowledge.entry * Retroknowledge.entry
