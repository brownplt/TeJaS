open Prelude
open Sig

module Pat = Dprle.Set
module rec StrobeImplB : (Strobe_sigs.STROBE_TYPS
                         with type extKind = BareImpl.kind
  with type extTyp = BareImpl.typ
  with type extBinding = BareImpl.binding
  with type pat = Pat.t) = Strobe_typ.Make (Pat) (BareImpl)
and BareImpl : (Bare_sigs.BARE_TYPS
               with type baseTyp = StrobeImplB.typ
  with type baseKind = StrobeImplB.kind
  with type baseBinding = StrobeImplB.binding) =
    Bare_types.Make (StrobeImplB)

module rec Bare : (Bare_sigs.BARE_ACTIONS
                     with type typ = BareImpl.typ
  with type kind = BareImpl.kind
  with type binding = BareImpl.binding
  with type env = BareImpl.env
  with type baseTyp = BareImpl.baseTyp
  with type baseKind = BareImpl.baseKind
  with type baseBinding = BareImpl.baseBinding) =
  Bare_types.MakeActions (StrobeB) (BareImpl)
and StrobeB : (Strobe_sigs.STROBE_ACTIONS
              with type typ = StrobeImplB.typ
  with type kind = StrobeImplB.kind
  with type binding = StrobeImplB.binding
  with type extTyp = StrobeImplB.extTyp
  with type extKind = StrobeImplB.extKind
  with type extBinding = StrobeImplB.extBinding
  with type pat = StrobeImplB.pat
  with type obj_typ = StrobeImplB.obj_typ
  with type presence = StrobeImplB.presence
  with type env = StrobeImplB.env) =
  Strobe_typ.MakeActions (Pat) (StrobeImplB) (Bare)

module StrobeModB = Strobe_typ.MakeModule (Pat) (StrobeB) (Bare)
module BareMod = Bare_types.MakeModule (StrobeModB) (Bare) 


module rec Bare_kind : (Bare_sigs.BARE_KINDING
                             with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)
  = Bare_kinding.Make (BareMod) (Strobe_kindB)
and Strobe_kindB : (Strobe_sigs.STROBE_KINDING
         with type typ = StrobeB.typ
  with type kind = StrobeB.kind
  with type binding = StrobeB.binding
  with type extTyp = StrobeB.extTyp
  with type extKind = StrobeB.extKind
  with type extBinding = StrobeB.extBinding
  with type obj_typ = StrobeB.obj_typ
  with type presence = StrobeB.presence
  with type pat = Pat.t
  with type env = StrobeB.env)
  = Strobe_kinding.Make (StrobeModB) (Bare_kind)

module ExpB = Typedjs_syntax.Exp (StrobeModB)
