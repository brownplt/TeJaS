open Prelude
open Sig

open Strobe_sigs

module Make : STROBE_TYP
module MakeActions :
  functor (Pat : SET) ->
    functor (STROBE : STROBE_TYPS with type pat = Pat.t) ->
      functor (EXT : EXT_TYP_SIG with type typ = STROBE.extTyp with type kind = STROBE.extKind with type binding = STROBE.extBinding with type baseTyp = STROBE.typ with type baseKind = STROBE.kind with type baseBinding = STROBE.binding) ->
        functor (Ext : TYP_ACTIONS with type typ = STROBE.extTyp with type kind = STROBE.extKind with type binding = STROBE.extBinding with type env = EXT.env) ->
          (STROBE_ACTIONS with type typ = STROBE.typ with type kind = STROBE.kind with type extTyp = STROBE.extTyp with type extKind = STROBE.extKind with type binding = STROBE.binding with type extBinding = STROBE.extBinding with type pat = STROBE.pat with type field = STROBE.field with type obj_typ = STROBE.obj_typ with type env = STROBE.env)
