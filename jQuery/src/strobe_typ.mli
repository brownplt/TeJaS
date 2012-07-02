open Prelude
open Sig

open Strobe_sigs

module Make : STROBE_TYP
module MakeActions :
  functor (Pat : SET) ->
    functor (STROBE : STROBE_TYPS with type pat = Pat.t) ->
      functor (Ext : EXT_TYP_ACTIONS
               with type typ = STROBE.extTyp
  with type kind = STROBE.extKind
  with type binding = STROBE.extBinding
  with type env = STROBE.env
  with type baseTyp = STROBE.typ
  with type baseKind = STROBE.kind
  with type baseBinding = STROBE.binding) ->
        (STROBE_ACTIONS
         with type typ = STROBE.typ
  with type kind = STROBE.kind
  with type extTyp = STROBE.extTyp
  with type extKind = STROBE.extKind
  with type binding = STROBE.binding
  with type extBinding = STROBE.extBinding
  with type pat = STROBE.pat
  with type obj_typ = STROBE.obj_typ
  with type env = STROBE.env)


module MakeModule :
  functor (Pat : SET) ->
    functor (STROBE : STROBE_ACTIONS with type pat = Pat.t) ->
      functor (EXT : EXT_TYP_ACTIONS   
               with type typ = STROBE.extTyp
  with type kind = STROBE.extKind
  with type binding = STROBE.extBinding
  with type baseTyp = STROBE.typ
  with type baseKind = STROBE.kind
  with type baseBinding = STROBE.binding
  with type env = STROBE.env) ->
        (STROBE_MODULE 
         with type typ = STROBE.typ
  with type kind = STROBE.kind
  with type binding = STROBE.binding
  with type extTyp = STROBE.extTyp
  with type extKind = STROBE.extKind
  with type extBinding = STROBE.extBinding
  with type pat = Pat.t
  with type env = STROBE.env)
