open Prelude
open Sig

module Pat = Dprle.Set
module rec StrobeImpl : (Strobe_sigs.STROBE_TYPS
                         with type extKind = BareImpl.kind
  with type extTyp = BareImpl.typ
  with type extBinding = BareImpl.binding
  with type pat = Pat.t) = Strobe_typ.Make (Pat) (BareImpl)
and BareImpl : (Bare_sigs.BARE_TYPS
               with type baseTyp = StrobeImpl.typ
  with type baseKind = StrobeImpl.kind
  with type baseBinding = StrobeImpl.binding) =
    Bare_types.Make (StrobeImpl)

module rec Bare : (Bare_sigs.BARE_ACTIONS
                     with type typ = BareImpl.typ
  with type kind = BareImpl.kind
  with type binding = BareImpl.binding
  with type env = BareImpl.env
  with type baseTyp = BareImpl.baseTyp
  with type baseKind = BareImpl.baseKind
  with type baseBinding = BareImpl.baseBinding) =
  Bare_types.MakeActions (Strobe) (BareImpl)
and Strobe : (Strobe_sigs.STROBE_ACTIONS
              with type typ = StrobeImpl.typ
  with type kind = StrobeImpl.kind
  with type binding = StrobeImpl.binding
  with type extTyp = StrobeImpl.extTyp
  with type extKind = StrobeImpl.extKind
  with type extBinding = StrobeImpl.extBinding
  with type pat = StrobeImpl.pat
  with type obj_typ = StrobeImpl.obj_typ
  with type presence = StrobeImpl.presence
  with type env = StrobeImpl.env) =
  Strobe_typ.MakeActions (Pat) (StrobeImpl) (Bare)

module StrobeMod = Strobe_typ.MakeModule (Pat) (Strobe) (Bare)
module BareMod = Bare_types.MakeModule (StrobeMod) (Bare) 


module rec Bare_kind : (Bare_sigs.BARE_KINDING
                             with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)
  = Bare_kinding.Make (BareMod) (Strobe_kind)
and Strobe_kind : (Strobe_sigs.STROBE_KINDING
         with type typ = Strobe.typ
  with type kind = Strobe.kind
  with type binding = Strobe.binding
  with type extTyp = Strobe.extTyp
  with type extKind = Strobe.extKind
  with type extBinding = Strobe.extBinding
  with type obj_typ = Strobe.obj_typ
  with type presence = Strobe.presence
  with type pat = Pat.t
  with type env = Strobe.env)
  = Strobe_kinding.Make (StrobeMod) (Bare_kind)

module Exp = Typedjs_syntax.Exp (StrobeMod)
