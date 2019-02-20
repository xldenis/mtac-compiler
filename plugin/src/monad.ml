(* MONADS !! :) *)
type 'a data = Val of (Environ.env * Evd.evar_map * 'a)
      | Err of (Environ.env * Evd.evar_map * 'a)


let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v
