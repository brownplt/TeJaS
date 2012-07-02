open Prelude
open Sig

open Strobe_typ
open JQuery_sigs
open Strobe_sigs

module MakeActions :
  functor (Strobe : STROBE_SUBTYPING) ->
    functor (JQ : JQUERY_ACTIONS
             with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env) ->
      functor (Css : Css.CSS with type t = JQ.sel) ->
          (JQUERY_SUBTYPING
           with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type sigma = JQ.sigma
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type env = JQ.env)
