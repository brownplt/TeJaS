open Prelude
open Sig
open Strobe_sigs
open Bare_sigs

module MakeExt :
  functor (Bare : BARE_MODULE) ->
    functor (BareKinding : BARE_KINDING
             with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env) ->
      functor (Env : TYP_ENV
               with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type env = Bare.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl) ->
        functor (Desugar : Bare_desugar.BARE_DESUGAR
                 with type typ = Bare.typ
                 with type writtyp = Typedjs_writtyp.WritTyp.t
  with type kind = Bare.kind) ->
        (BARE_TYP_ENV
         with type typ = Env.typ
  with type kind = Env.kind
  with type binding = Env.binding
  with type env = Env.env
  with type env_decl = Env.env_decl)
