module CoqUnit :
sig
  val mkTT : EConstr.constr lazy_t
end

val reify : Environ.env -> Evd.evar_map -> EConstr.constr -> EConstr.constr lazy_t
