open Prelude
open Sig
open Strobe_sigs
open TypeScript_sigs

module MakeExt :
  functor (TypeScript : TYPESCRIPT_MODULE) ->
    functor (TypeScriptKinding : TYPESCRIPT_KINDING
             with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env) ->
      functor (Env : TYP_ENV
               with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type env = TypeScript.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl) ->
        functor (Desugar : TypeScript_desugar.TYPESCRIPT_DESUGAR
                 with type typ = TypeScript.typ
                 with type writtyp = Typedjs_writtyp.WritTyp.t
  with type kind = TypeScript.kind) ->
        (TYPESCRIPT_TYP_ENV
         with type typ = Env.typ
  with type kind = Env.kind
  with type binding = Env.binding
  with type env = Env.env
  with type env_decl = Env.env_decl)
