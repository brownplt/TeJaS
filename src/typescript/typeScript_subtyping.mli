open Prelude
open Sig

open Strobe_typ
open TypeScript_sigs
open Strobe_sigs

module MakeActions :
  functor (Strobe : STROBE_SUBTYPING) ->
    functor (TypeScript : TYPESCRIPT_MODULE
             with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env) ->
      functor (Env : TYPESCRIPT_TYP_ENV
               with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type env = TypeScript.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl) ->
      (TYPESCRIPT_SUBTYPING
       with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env)
