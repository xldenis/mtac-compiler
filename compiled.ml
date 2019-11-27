open Nativevalues
open Mtaclite__Nativecode
open Mtaclite__Nativelib
open Nativeconv
open Mtaclite__Unify
open Declaremods

let symbols_tbl = get_symbols ()

let indaccu_list_0 = mk_ind_accu (get_ind symbols_tbl 0) [||]

type ind_list_0 =
  | Accu_list_0 of Nativevalues.t
  | Construct_list_0_0
  | Construct_list_0_1 of Nativevalues.t * Nativevalues.t

let construct_list_0_0 (x_params_0 : Nativevalues.t) : Nativevalues.t = Obj.magic Construct_list_0_0

let construct_list_0_1 (x_params_0 : Nativevalues.t) (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) :
    Nativevalues.t =
  Obj.magic (Construct_list_0_1 (x_arg_0, x_arg_1))

let indaccu_nat_0 = mk_ind_accu (get_ind symbols_tbl 1) [||]

type ind_nat_0 = Accu_nat_0 of Nativevalues.t | Construct_nat_0_0 | Construct_nat_0_1 of Nativevalues.t

let construct_nat_0_0 : Nativevalues.t = Obj.magic Construct_nat_0_0

let construct_nat_0_1 (x_arg_0 : Nativevalues.t) : Nativevalues.t = Obj.magic (Construct_nat_0_1 x_arg_0)

let indaccu_Mtac_0 = mk_ind_accu (get_ind symbols_tbl 2) [||]

type ind_Mtac_0 =
  | Accu_Mtac_0 of Nativevalues.t
  | Construct_Mtac_0_0 of Nativevalues.t
  | Ret of Nativevalues.t * Nativevalues.t
  | Bind of Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Construct_Mtac_0_3 of Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Construct_Mtac_0_4 of
      Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Construct_Mtac_0_5 of
      Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
  | Construct_Mtac_0_6 of Nativevalues.t * Nativevalues.t
  | Construct_Mtac_0_7 of Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Evar of Nativevalues.t
  | Construct_Mtac_0_9 of Nativevalues.t * Nativevalues.t * Nativevalues.t
  | Ret0 of Nativevalues.t * Nativevalues.t * Nativevalues.t * Nativevalues.t

let construct_Mtac_0_0 (x_arg_0 : Nativevalues.t) : Nativevalues.t = Obj.magic (Construct_Mtac_0_0 x_arg_0)

let construct_Mtac_0_1 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Ret (x_arg_0, x_arg_1))

let construct_Mtac_0_2 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) (x_arg_2 : Nativevalues.t)
    (x_arg_3 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Bind (x_arg_0, x_arg_1, x_arg_2, x_arg_3))

let construct_Mtac_0_3 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) (x_arg_2 : Nativevalues.t) :
    Nativevalues.t =
  Obj.magic (Construct_Mtac_0_3 (x_arg_0, x_arg_1, x_arg_2))

let construct_Mtac_0_4 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) (x_arg_2 : Nativevalues.t)
    (x_arg_3 : Nativevalues.t) (x_arg_4 : Nativevalues.t) (x_arg_5 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Construct_Mtac_0_4 (x_arg_0, x_arg_1, x_arg_2, x_arg_3, x_arg_4, x_arg_5))

let construct_Mtac_0_5 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) (x_arg_2 : Nativevalues.t)
    (x_arg_3 : Nativevalues.t) (x_arg_4 : Nativevalues.t) (x_arg_5 : Nativevalues.t) (x_arg_6 : Nativevalues.t)
    (x_arg_7 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Construct_Mtac_0_5 (x_arg_0, x_arg_1, x_arg_2, x_arg_3, x_arg_4, x_arg_5, x_arg_6, x_arg_7))

let construct_Mtac_0_6 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Construct_Mtac_0_6 (x_arg_0, x_arg_1))

let construct_Mtac_0_7 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) (x_arg_2 : Nativevalues.t) :
    Nativevalues.t =
  Obj.magic (Construct_Mtac_0_7 (x_arg_0, x_arg_1, x_arg_2))

let construct_Mtac_0_8 (x_arg_0 : Nativevalues.t) : Nativevalues.t = Obj.magic (Evar x_arg_0)

let construct_Mtac_0_9 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) (x_arg_2 : Nativevalues.t) :
    Nativevalues.t =
  Obj.magic (Construct_Mtac_0_9 (x_arg_0, x_arg_1, x_arg_2))

let construct_Mtac_0_10 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) (x_arg_2 : Nativevalues.t)
    (x_arg_3 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Ret0 (x_arg_0, x_arg_1, x_arg_2, x_arg_3))

let indaccu_True_0 = mk_ind_accu (get_ind symbols_tbl 3) [||]

type ind_True_0 = Accu_True_0 of Nativevalues.t | Construct_True_0_0

let construct_True_0_0 : Nativevalues.t = Obj.magic Construct_True_0_0

let indaccu_option_0 = mk_ind_accu (get_ind symbols_tbl 4) [||]

type ind_option_0 = Accu_option_0 of Nativevalues.t | Construct_option_0_0 of Nativevalues.t | Construct_option_0_1

let construct_option_0_0 (x_params_0 : Nativevalues.t) (x_arg_0 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Construct_option_0_0 x_arg_0)

let construct_option_0_1 (x_params_0 : Nativevalues.t) : Nativevalues.t = Obj.magic Construct_option_0_1

let indaccu_eq_0 = mk_ind_accu (get_ind symbols_tbl 5) [||]

type ind_eq_0 = Accu_eq_0 of Nativevalues.t | Construct_eq_0_0

let construct_eq_0_0 (x_params_0 : Nativevalues.t) (x_params_1 : Nativevalues.t) : Nativevalues.t =
  Obj.magic Construct_eq_0_0

let fixtype_app_0 (x_A_1 : Nativevalues.t) =
  [| mk_prod_accu (get_name symbols_tbl 7) (indaccu_list_0 x_A_1) (fun (x_l_2 : Nativevalues.t) ->
         mk_prod_accu (get_name symbols_tbl 6) (indaccu_list_0 x_A_1) (fun (x_m_3 : Nativevalues.t) ->
             indaccu_list_0 x_A_1 ) ) |]

let pred_app_0 (x_A_8 : Nativevalues.t) (x_l_7 : Nativevalues.t) = indaccu_list_0 x_A_8

(* Hash = 3571850128003727268 *)
let rec case_app_0 (x_A_14 : Nativevalues.t) (x_app_13 : Nativevalues.t) (x_m_10 : Nativevalues.t)
    (x_anonymous_9 : Nativevalues.t) =
  match Obj.magic x_anonymous_9 with
  | Accu_list_0 _ ->
      mk_sw_accu (get_match symbols_tbl 8) (cast_accu x_anonymous_9) (pred_app_0 x_A_14)
        (case_app_0 x_A_14 x_app_13 x_m_10)
  | Construct_list_0_0 ->
      x_m_10
  | Construct_list_0_1 (x_a_11, x_l1_12) ->
      (Obj.magic (Construct_list_0_1 (x_a_11, x_app_13 x_l1_12 x_m_10)) : Nativevalues.t)

let norm_app_0 (x_A_15 : Nativevalues.t) (x_app_4 : Nativevalues.t) (x_l_5 : Nativevalues.t) (x_m_6 : Nativevalues.t) =
  case_app_0 x_A_15 x_app_4 x_m_6 x_l_5

let normtbl_app_0 (x_A_15 : Nativevalues.t) = [|norm_app_0 x_A_15|]

let const_app (x_A_0 : Nativevalues.t) =
  let rec x_app_16 (x_l_5 : Nativevalues.t) (x_m_6 : Nativevalues.t) =
    match Obj.magic x_l_5 with
    | Accu_list_0 _ ->
        mk_fix_accu [|0|] 0 (fixtype_app_0 x_A_0) (normtbl_app_0 x_A_0) x_l_5 x_m_6
    | Construct_list_0_0 ->
        x_m_6
    | Construct_list_0_1 (x_a_11, x_l1_12) ->
        (Obj.magic (Construct_list_0_1 (x_a_11, x_app_16 x_l1_12 x_m_6)) : Nativevalues.t)
  in
  x_app_16

let indaccu_NCoq_Strings_String_string_0 = mk_ind_accu (get_ind symbols_tbl 9) [||]

type ind_NCoq_Strings_String_string_0 =
  | Accu_NCoq_Strings_String_string_0 of Nativevalues.t
  | Construct_NCoq_Strings_String_string_0_0
  | Construct_NCoq_Strings_String_string_0_1 of Nativevalues.t * Nativevalues.t

let construct_NCoq_Strings_String_string_0_0 : Nativevalues.t = Obj.magic Construct_NCoq_Strings_String_string_0_0

let construct_NCoq_Strings_String_string_0_1 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t) : Nativevalues.t =
  Obj.magic (Construct_NCoq_Strings_String_string_0_1 (x_arg_0, x_arg_1))

let indaccu_NCoq_Strings_Ascii_ascii_0 = mk_ind_accu (get_ind symbols_tbl 10) [||]

type ind_NCoq_Strings_Ascii_ascii_0 =
  | Accu_NCoq_Strings_Ascii_ascii_0 of Nativevalues.t
  | Construct_NCoq_Strings_Ascii_ascii_0_0 of
      Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t
      * Nativevalues.t

let construct_NCoq_Strings_Ascii_ascii_0_0 (x_arg_0 : Nativevalues.t) (x_arg_1 : Nativevalues.t)
    (x_arg_2 : Nativevalues.t) (x_arg_3 : Nativevalues.t) (x_arg_4 : Nativevalues.t) (x_arg_5 : Nativevalues.t)
    (x_arg_6 : Nativevalues.t) (x_arg_7 : Nativevalues.t) : Nativevalues.t =
  Obj.magic
    (Construct_NCoq_Strings_Ascii_ascii_0_0 (x_arg_0, x_arg_1, x_arg_2, x_arg_3, x_arg_4, x_arg_5, x_arg_6, x_arg_7))

let indaccu_bool_0 = mk_ind_accu (get_ind symbols_tbl 11) [||]

type ind_bool_0 = Accu_bool_0 of Nativevalues.t | Construct_bool_0_0 | Construct_bool_0_1

let construct_bool_0_0 : Nativevalues.t = Obj.magic Construct_bool_0_0

let construct_bool_0_1 : Nativevalues.t = Obj.magic Construct_bool_0_1

let pred_lazyUnify'_1 (x_eq_21 : Nativevalues.t) = indaccu_Mtac_0 indaccu_True_0

(* Hash = 4216123932178279499 *)
let rec case_lazyUnify'_1 (x_anonymous_22 : Nativevalues.t) =
  match Obj.magic x_anonymous_22 with
  | Accu_option_0 _ ->
      mk_sw_accu (get_match symbols_tbl 13) (cast_accu x_anonymous_22) pred_lazyUnify'_1 case_lazyUnify'_1
  | Construct_option_0_0 _ ->
      (Obj.magic (Ret (indaccu_True_0, (Obj.magic Construct_True_0_0 : Nativevalues.t))) : Nativevalues.t)
  | Construct_option_0_1 ->
      (Obj.magic (Construct_Mtac_0_6 (indaccu_True_0, get_value symbols_tbl 12)) : Nativevalues.t)

let const_NLazyCompile_lazyUnify' (x_arg_17 : Nativevalues.t) : Nativevalues.t =
  Obj.magic
    (Bind
       ( indaccu_list_0 indaccu_nat_0
       , indaccu_True_0
       , (Obj.magic (Evar (indaccu_list_0 indaccu_nat_0)) : Nativevalues.t)
       , fun (x_x_18 : Nativevalues.t) ->
           ( Obj.magic
               (Bind
                  ( indaccu_list_0 indaccu_nat_0
                  , indaccu_True_0
                  , (Obj.magic (Evar (indaccu_list_0 indaccu_nat_0)) : Nativevalues.t)
                  , fun (x_y_19 : Nativevalues.t) ->
                      ( Obj.magic
                          (Bind
                             ( indaccu_option_0
                                 (indaccu_eq_0 (indaccu_list_0 indaccu_nat_0) (const_app indaccu_nat_0 x_x_18 x_y_19)
                                    x_arg_17)
                             , indaccu_True_0
                             , ( Obj.magic
                                   (Construct_Mtac_0_3
                                      (indaccu_list_0 indaccu_nat_0, const_app indaccu_nat_0 x_x_18 x_y_19, x_arg_17))
                                 : Nativevalues.t )
                             , fun (x_eq_20 : Nativevalues.t) ->
                                 match Obj.magic x_eq_20 with
                                 | Accu_option_0 _ ->
                                     mk_sw_accu (get_match symbols_tbl 13) (cast_accu x_eq_20) pred_lazyUnify'_1
                                       case_lazyUnify'_1
                                 | Construct_option_0_0 _ ->
                                     ( Obj.magic (Ret (indaccu_True_0, (Obj.magic Construct_True_0_0 : Nativevalues.t)))
                                       : Nativevalues.t )
                                 | Construct_option_0_1 ->
                                     ( Obj.magic (Construct_Mtac_0_6 (indaccu_True_0, get_value symbols_tbl 12))
                                       : Nativevalues.t ) ))
                        : Nativevalues.t ) ))
             : Nativevalues.t ) ))

let t1 =
  const_NLazyCompile_lazyUnify'
    (mk_constant_accu (get_const symbols_tbl 16) [||] indaccu_nat_0 (get_value symbols_tbl 14)
       (get_value symbols_tbl 15))

let _ = rt1 := t1
