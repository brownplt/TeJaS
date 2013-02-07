open Prelude
open Sig

open Strobe_typ
open Bare_sigs
open Strobe_sigs

module MakeActions :
  functor (Strobe : STROBE_SUBTYPING) ->
    functor (Bare : BARE_MODULE
             with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env) ->
      functor (Env : BARE_TYP_ENV
               with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type env = Bare.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl) ->
      (BARE_SUBTYPING
       with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)
