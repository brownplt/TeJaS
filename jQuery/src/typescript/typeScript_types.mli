open Prelude
open Sig

open Strobe_typ
open TypeScript_sigs
open Strobe_sigs

module Make : TYPESCRIPT_TYP
module MakeActions :
  functor (Strobe : STROBE_ACTIONS) ->
    functor (TypeScript : TYPESCRIPT_TYPS
             with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env) ->
          (TYPESCRIPT_ACTIONS
           with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env)

module MakeModule :
  functor (Strobe : STROBE_MODULE) ->
    functor (TypeScript : TYPESCRIPT_ACTIONS
             with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env) ->
        (TYPESCRIPT_MODULE
       with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env
  with module Strobe = Strobe)
