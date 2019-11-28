open Nativelambda
open Pp

(*
  During compilation we go through Coq's nativelambda representation at one point. To debug problems during that phase
  it's very useful to have a pretty printer that actually lets us know something about the form of the lambda terms
  we're generating (ie whether any callType calls remain after compilation!).

  Only a portion of the cases are implemented and can be extended as needed
*)

let rec pp_lambda env sigma l : Pp.t  =
  begin match l with
  | Lrel _ -> str "Lrel"
  | Lvar _ -> str "Lvar"
  | Lmeta _ -> str "Lmeta"
  | Levar _ -> str "Levar"
  | Lprod _ -> str "Lprod"
  | Llam (bndrs, body) ->
      str "LLam" ++ surround (
        prlist_with_sep pr_comma pp_binder (Array.to_list bndrs) ++ pr_comma () ++ pp_lambda env sigma body)
  | Lrec _ -> str "Lrec"
  | Llet _ -> str "Llet"
  | Lapp (f, args) -> str "Lapp" ++ surround (
      pp_lambda env sigma f ++ pr_comma () ++ prlist_with_sep pr_comma (pp_lambda env sigma) (Array.to_list args)
    )
  | Lconst (_, c) -> str "Lconst" ++ surround (Printer.pr_pconstant env sigma c)
  | Lconst_accu (_, c) -> str "Lconst_accu" ++ surround (Printer.pr_pconstant env sigma c)
  | Lproj _ -> str "Lproj"
  | Lprim _ -> str "Lprim"
  | Lcase _ -> str "Lcase"
  | Lif _ -> str "Lif"
  | Lfix _ -> str "Lfix"
  | Lcofix _ -> str "Lcofix"
  | Lmakeblock (_, c, i, l) -> str "Lmakeblock" ++ surround (
    Printer.pr_pconstructor env sigma c ++ pr_comma () ++
    int i ++ pr_comma () ++
    prlist_with_sep pr_comma (pp_lambda env sigma) (Array.to_list l))
  | Lconstruct _ -> str "Lconstruct"
  | Luint _ -> str "Luint"
  | Lval (v) -> str "Lval"
  | Lsort _ -> str "Lsort"
  | Lind (_, i) -> str "Lind" ++ surround (Printer.pr_pinductive env sigma i)
  | Llazy _ -> str "Llazy"
  | Lforce _ -> str "Lforce"
  end
and pp_binder binder =  Names.Name.print (Context.binder_name binder)
