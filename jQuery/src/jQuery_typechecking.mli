open Prelude
open Sig

module Make :
  functor (JQ : JQuery_sigs.JQUERY_MODULE) ->
    functor (Exp : Typedjs_syntax.EXP with module Typs = JQ.Strobe) ->
      functor (Env : JQuery_sigs.JQUERY_TYP_ENV
               with type typ = JQ.typ
  with type kind = JQ.kind
  with type sigma = JQ.sigma
  with type multiplicity = JQ.multiplicity
  with type binding = JQ.binding
  with type env = JQ.env) ->
        functor (Sub : JQuery_sigs.JQUERY_SUBTYPING
                 with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type env = JQ.env) ->
          functor (Kind : JQuery_sigs.JQUERY_KINDING
                   with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type env = JQ.env) ->
            functor (StrobeTC : Strobe_sigs.STROBE_TYPECHECKING
                     with type typ = JQ.baseTyp
  with type kind = JQ.baseKind
  with type binding = JQ.baseBinding
  with type extTyp = JQ.typ
  with type extKind = JQ.kind
  with type extBinding = JQ.binding
  with type exp = Exp.exp
  with type env = JQ.env) ->
              (JQuery_sigs.JQUERY_TYPECHECKING
               with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type sigma = JQ.sigma
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type env = JQ.env
  with type exp = Exp.exp)
