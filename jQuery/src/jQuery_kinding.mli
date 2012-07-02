open Prelude
open Sig

open Strobe_typ
open JQuery_sigs
open Strobe_sigs

module Make :
  functor (JQuery : JQUERY_MODULE) ->
    functor (StrobeKind : STROBE_KINDING
             with type typ = JQuery.baseTyp
  with type kind = JQuery.baseKind
  with type binding = JQuery.baseBinding
  with type extTyp = JQuery.typ
  with type extKind = JQuery.kind
  with type extBinding = JQuery.binding
  with type env = JQuery.env) ->
      (JQUERY_KINDING
       with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type binding = JQuery.binding
  with type multiplicity = JQuery.multiplicity
  with type sigma = JQuery.sigma
  with type baseTyp = JQuery.baseTyp
  with type baseKind = JQuery.baseKind
  with type baseBinding = JQuery.baseBinding
  with type env = JQuery.env
  with type sel = JQuery.sel)
