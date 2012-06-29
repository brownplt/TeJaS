open Prelude
open Sig

open Strobe_sigs

module Make : STROBE_TYP
module MakeActions :
  functor (Pat : SET) ->
    functor (STROBE : STROBE_TYPS with type pat = Pat.t) ->
      functor (EXT : TYP_ACTIONS with type typ = STROBE.extTyp with type kind = STROBE.extKind) ->
        (STROBE_ACTIONS with type typ = STROBE.typ with type kind = STROBE.kind with type extTyp = STROBE.extTyp with type extKind = STROBE.extKind with type pat = STROBE.pat with type field = STROBE.field with type obj_typ = STROBE.obj_typ)
