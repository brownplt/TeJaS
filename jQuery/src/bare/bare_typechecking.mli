open Prelude
open Sig

module Make :
  functor (Bare : Bare_sigs.BARE_MODULE) ->
    functor (Exp : Typedjs_syntax.EXP with module Typs = Bare.Strobe) ->
      functor (Env : Bare_sigs.BARE_TYP_ENV
               with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type env = Bare.env) ->
        functor (Sub : Bare_sigs.BARE_SUBTYPING
                 with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env) ->
          functor (Kind : Bare_sigs.BARE_KINDING
                   with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env) ->
            functor (StrobeTC : Strobe_sigs.STROBE_TYPECHECKING
                     with type typ = Bare.baseTyp
  with type kind = Bare.baseKind
  with type binding = Bare.baseBinding
  with type extTyp = Bare.typ
  with type extKind = Bare.kind
  with type extBinding = Bare.binding
  with type exp = Exp.exp
  with type env = Bare.env) ->
              (Bare_sigs.BARE_TYPECHECKING
               with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env
  with type exp = Exp.exp)
