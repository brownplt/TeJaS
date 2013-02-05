open Prelude
open Sig

open Strobe_typ
open Bare_sigs
open Strobe_sigs

module Make :
  functor (Bare : BARE_MODULE) ->
    functor (StrobeKind : STROBE_KINDING
             with type typ = Bare.baseTyp
  with type kind = Bare.baseKind
  with type binding = Bare.baseBinding
  with type extTyp = Bare.typ
  with type extKind = Bare.kind
  with type extBinding = Bare.binding
  with type env = Bare.env) ->
      (BARE_KINDING
       with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)
