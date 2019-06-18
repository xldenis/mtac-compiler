open Monad
open EConstr

val compile :
  Environ.env ->
  Evd.evar_map ->
  'a ->
  constr ->
  (constr lazy_t) data
