module CoqUnit :
sig
  val mkTT : EConstr.constr lazy_t
end

type data = Val of (Environ.env * Evd.evar_map * EConstr.constr lazy_t)
      | Err of (Environ.env * Evd.evar_map * EConstr.constr lazy_t)

val interpret :
  Environ.env ->
  Evd.evar_map ->
  EConstr.constr ->
  EConstr.constr ->
  data
