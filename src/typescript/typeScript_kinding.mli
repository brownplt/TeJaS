open Prelude
open Sig

open Strobe_typ
open TypeScript_sigs
open Strobe_sigs

module Make :
  functor (TypeScript : TYPESCRIPT_MODULE) ->
    functor (StrobeKind : STROBE_KINDING
             with type typ = TypeScript.baseTyp
  with type kind = TypeScript.baseKind
  with type binding = TypeScript.baseBinding
  with type extTyp = TypeScript.typ
  with type extKind = TypeScript.kind
  with type extBinding = TypeScript.binding
  with type env = TypeScript.env) ->
      (TYPESCRIPT_KINDING
       with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env)
