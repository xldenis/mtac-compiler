open Monad
open EConstr

val interpret :
  Environ.env ->
  Evd.evar_map ->
  constr ->
  constr ->
  (constr lazy_t) data
