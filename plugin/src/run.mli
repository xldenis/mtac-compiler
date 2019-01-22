module CoqUnit :
sig
  val mkTT : EConstr.constr lazy_t
end

val interpret : Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr lazy_t
