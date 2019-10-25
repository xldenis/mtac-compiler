(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
open Names
open Constr
open Declarations
open Environ
open Nativelambda
open Nativecode

type code_location_update
type code_location_updates
type linkable_code = global list * code_location_updates

val empty_updates : code_location_updates

val register_native_file : string -> unit

val compile_constant_field : Environ.env -> string -> Constant.t ->
  global list -> constant_body -> global list

val mk_conv_code : Environ.env -> evars -> string -> constr -> constr -> linkable_code
val mk_norm_code : Environ.env -> evars -> string -> constr -> linkable_code

val mk_library_header : DirPath.t -> global list

val update_locations : code_location_updates -> unit

val add_header_comment : global list -> string -> global list

val compile_tactic : Environ.env -> Evd.evar_map -> string -> EConstr.t -> linkable_code
