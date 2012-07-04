open Prelude
open Sig
open Strobe_sigs
open JQuery_sigs

module MakeExt :
  functor (JQuery : JQUERY_MODULE) ->
    functor (JQueryKinding : JQUERY_KINDING
             with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type multiplicity = JQuery.multiplicity
  with type sigma = JQuery.sigma
  with type binding = JQuery.binding
  with type baseTyp = JQuery.baseTyp
  with type baseKind = JQuery.baseKind
  with type baseBinding = JQuery.baseBinding
  with type env = JQuery.env) ->
      functor (Env : TYP_ENV
               with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type binding = JQuery.binding
  with type env = JQuery.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl) ->
        functor (Desugar : Typedjs_desugar.DESUGAR
                 with type typ = JQuery.typ
  with type kind = JQuery.kind) ->
        (JQUERY_TYP_ENV
         with type typ = Env.typ
  with type kind = Env.kind
  with type binding = Env.binding
  with type sigma = JQuery.sigma
  with type env = Env.env
  with type env_decl = Env.env_decl)
