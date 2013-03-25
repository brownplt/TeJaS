open Prelude
open Sig
open Strobe_sigs

module Make :
  functor (Strobe : STROBE_MODULE) ->
    functor (ExtKinding : EXT_KINDING
             with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type env = Strobe.env) ->
      (STROBE_KINDING
       with type typ = Strobe.typ
  with type kind = Strobe.kind
  with type binding = Strobe.binding
  with type extTyp = Strobe.extTyp
  with type extKind = Strobe.extKind
  with type extBinding = Strobe.extBinding
  with type obj_typ = Strobe.obj_typ
  with type presence = Strobe.presence
  with type pat = Strobe.pat
  with type env = Strobe.env)
