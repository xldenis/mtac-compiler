(* MONADS !! :) *)
type interp_state =
  { fresh_counter : int ref;
    metas : int
  }

let fresh_name (nm : string) (s : interp_state) : Names.Id.t =
  let counter = s.fresh_counter in
  let curr_fresh = !counter in
  let base = Names.Id.of_string (nm ^ string_of_int curr_fresh) in
  let _ = counter := !counter + 1 in
  base

type 'a data = Val of (interp_state * Environ.env * Evd.evar_map * 'a)
      | Err of (interp_state * Environ.env * Evd.evar_map * 'a)


let (>>=) v g =
  match v with
    | Val v' -> g v'
    | _ -> v
