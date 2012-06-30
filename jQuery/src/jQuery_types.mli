open Prelude
open Sig

open Strobe_typ
open JQuery_sigs
open Strobe_sigs

module Make : JQUERY_TYP
module MakeActions :
  functor (STROBE : STROBE_TYPS) ->
    functor (JQ : JQUERY_TYPS
             with type baseTyp = STROBE.typ
  with type baseKind = STROBE.kind
  with type baseBinding = STROBE.binding
  with type typ = STROBE.extTyp
  with type kind = STROBE.extKind
  with type binding = STROBE.extBinding) ->
      functor (Css : Css.CSS with type t = JQ.sel) ->
        functor (Strobe : STROBE_ACTIONS
                 with type typ = STROBE.typ
  with type kind = STROBE.kind
  with type binding = STROBE.binding
  with type extTyp = STROBE.extTyp
  with type extKind = STROBE.extKind
  with type extBinding = STROBE.extBinding
  with type field = STROBE.field
  with type obj_typ = STROBE.obj_typ
  with type env = STROBE.env) -> 
          (JQUERY_ACTIONS
           with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type binding = JQ.binding)

