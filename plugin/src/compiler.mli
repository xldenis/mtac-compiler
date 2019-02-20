val compile : Environ.env -> Evd.evar_map -> 'a -> EConstr.constr -> EConstr.t lazy_t
val construct_of_constr : bool -> Environ.env -> Evd.evar_map -> int -> Retroknowledge.entry -> Retroknowledge.entry * Retroknowledge.entry
