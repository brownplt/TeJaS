open Prelude
open Sig

open Strobe_typ
open JQuery_sigs
open Strobe_sigs

module Make : JQUERY_TYP
module MakeActions :
  functor (STROBE : STROBE_TYPS) ->
    functor (JQ : JQUERY_TYPS with type strobeTyp = STROBE.typ with type strobeKind = STROBE.kind
  with type typ = STROBE.extTyp with type kind = STROBE.extKind) ->
      functor (Css : Css.CSS with type t = JQ.sel) ->
        functor (Strobe : STROBE_ACTIONS with type typ = STROBE.typ with type kind = STROBE.kind with type extTyp = STROBE.extTyp with type extKind = STROBE.extKind) -> 
          (JQUERY_ACTIONS with type typ = JQ.typ with type kind = JQ.kind with type multiplicity = JQ.multiplicity)

