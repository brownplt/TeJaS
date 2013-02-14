open Prelude
open Sig

module Make :
  functor (TypeScript : TypeScript_sigs.TYPESCRIPT_MODULE) ->
    functor (Exp : Typedjs_syntax.EXP with module Typs = TypeScript.Strobe) ->
      functor (Env : TypeScript_sigs.TYPESCRIPT_TYP_ENV
               with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type env = TypeScript.env) ->
        functor (Sub : TypeScript_sigs.TYPESCRIPT_SUBTYPING
                 with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env) ->
          functor (Kind : TypeScript_sigs.TYPESCRIPT_KINDING
                   with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env) ->
            functor (StrobeTC : Strobe_sigs.STROBE_TYPECHECKING
                     with type typ = TypeScript.baseTyp
  with type kind = TypeScript.baseKind
  with type binding = TypeScript.baseBinding
  with type extTyp = TypeScript.typ
  with type extKind = TypeScript.kind
  with type extBinding = TypeScript.binding
  with type exp = Exp.exp
  with type env = TypeScript.env) ->
              (TypeScript_sigs.TYPESCRIPT_TYPECHECKING
               with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env
  with type exp = Exp.exp)
