open Prelude
open Sig

open Strobe_typ
open Bare_sigs
open Strobe_sigs

module Make : BARE_TYP
module MakeActions :
  functor (Strobe : STROBE_ACTIONS) ->
    functor (Bare : BARE_TYPS
             with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env) ->
          (BARE_ACTIONS
           with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)

module MakeModule :
  functor (Strobe : STROBE_MODULE) ->
    functor (Bare : BARE_ACTIONS
             with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env) ->
        (BARE_MODULE
       with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env
  with module Strobe = Strobe)
