open Monad
open EConstr

val run :
  Environ.env ->
  Evd.evar_map ->
  constr ->
  constr ->
  (constr lazy_t) data

val abs : ?mkprod:bool -> (Environ.env * Evd.evar_map) -> types -> types -> constr -> constr -> constr

val clean_unused_metas :
           Evd.evar_map -> Evar.Set.t -> Evd.etypes -> Evd.evar_map
