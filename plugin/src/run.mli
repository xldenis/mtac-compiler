open Monad
open EConstr

val interpret :
  Environ.env ->
  Evd.evar_map ->
  constr ->
  constr ->
  (constr lazy_t) data

val abs : ?mkprod:bool -> (Environ.env * Evd.evar_map) -> types -> types -> constr -> constr -> constr

val subst_evar :
           Evd.evar_map ->
           Evd.etypes -> Evd.etypes -> Evd.etypes -> Evd.etypes
