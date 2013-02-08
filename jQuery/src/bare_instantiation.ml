open Bare_syntax

module B = BareImpl
module S = StrobeImpl
module BareDesugar = Bare_desugar.Make (StrobeMod) (BareMod)
module SEnv = Strobe_env.Make (StrobeMod) (Strobe_kind) (BareDesugar)
module BareEnv = Bare_env.MakeExt (BareMod) (Bare_kind) (SEnv) (BareDesugar)

module rec BareSub : (Bare_sigs.BARE_SUBTYPING
                        with type typ = BareImpl.typ
  with type kind = BareImpl.kind
  with type binding = BareImpl.binding
  with type env = BareImpl.env
  with type baseTyp = BareImpl.baseTyp
  with type baseKind = BareImpl.baseKind
  with type baseBinding = BareImpl.baseBinding) =
  Bare_subtyping.MakeActions (StrobeSub) (BareMod) (BareEnv)
and StrobeSub : (Strobe_sigs.STROBE_SUBTYPING
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
  Strobe_subtyping.MakeActions (StrobeMod) (BareSub) (BareEnv)


module DummySemicfa = struct
  type env = BareEnv.env
  type exp = Exp.exp
  let semicfa _ _ e = e
end
module DummyStatic = struct
  type typ = BareEnv.typ
  type env = BareEnv.env
  let static _ _ t = t
end

module rec StrobeTC : (Strobe_sigs.STROBE_TYPECHECKING
                with type typ = StrobeImpl.typ
  with type kind = StrobeImpl.kind
  with type binding = StrobeImpl.binding
  with type extTyp = StrobeImpl.extTyp
  with type extKind = StrobeImpl.extKind
  with type extBinding = StrobeImpl.extBinding
  with type pat = StrobeImpl.pat
  with type obj_typ = StrobeImpl.obj_typ
  with type presence = StrobeImpl.presence
  with type env = StrobeImpl.env
  with type exp = Exp.exp) =
  Strobe_typechecking.Make (StrobeMod) (Exp) (BareEnv) (StrobeSub) (Bare_kind) (DummySemicfa) (DummyStatic) (BareTC)
and BareTC : (Bare_sigs.BARE_TYPECHECKING
                       with type typ = BareImpl.typ
  with type kind = BareImpl.kind
  with type binding = BareImpl.binding
  with type env = BareImpl.env
  with type baseTyp = BareImpl.baseTyp
  with type baseKind = BareImpl.baseKind
  with type baseBinding = BareImpl.baseBinding
  with type exp = Exp.exp) =
  Bare_typechecking.Make (BareMod) (Exp) (BareEnv) (BareSub) (Bare_kind) (StrobeTC)

