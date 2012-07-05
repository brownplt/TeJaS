open Prelude
open Sig

module Make : 
  functor (Typ : Strobe_sigs.STROBE_MODULE) ->
    functor (Exp : Typedjs_syntax.EXP with module Typs = Typ) ->
      functor (Env : TYP_ENV
               with type typ = Typ.extTyp
  with type kind = Typ.extKind
  with type binding = Typ.extBinding
  with type env = Typ.env) ->
        functor (Sub : Strobe_sigs.STROBE_SUBTYPING
                 with type typ = Typ.typ
  with type kind = Typ.kind
  with type binding = Typ.binding
  with type extTyp = Typ.extTyp
  with type extKind = Typ.extKind
  with type extBinding = Typ.extBinding
  with type pat = Typ.pat
  with type obj_typ = Typ.obj_typ
  with type presence = Typ.presence
  with type env = Typ.env) ->
          functor (Kind : EXT_KINDING
                   with type baseTyp = Typ.typ
  with type baseKind = Typ.kind
  with type baseBinding = Typ.binding
  with type typ = Typ.extTyp
  with type kind = Typ.extKind
  with type binding = Typ.extBinding
  with type env = Typ.env) ->
            functor (Semicfa : SEMICFA
                     with type env = Typ.env
  with type exp = Exp.exp) ->
              functor (Static : Typedjs_syntax.STATIC
                       with type env = Env.env
  with type typ = Env.typ) ->
                functor (ExtTC : EXT_TYPECHECKING
                         with type typ = Typ.extTyp
  with type kind = Typ.extKind
  with type binding = Typ.extBinding
  with type baseTyp = Typ.typ
  with type baseKind = Typ.kind
  with type baseBinding = Typ.binding
  with type exp = Exp.exp
  with type env = Typ.env) -> 
                  (Strobe_sigs.STROBE_TYPECHECKING
                   with type typ = Typ.typ
  with type kind = Typ.kind
  with type binding = Typ.binding
  with type extTyp = Typ.extTyp
  with type extKind = Typ.extKind
  with type extBinding = Typ.extBinding
  with type pat = Typ.pat
  with type obj_typ = Typ.obj_typ
  with type presence = Typ.presence
  with type exp = Exp.exp)
