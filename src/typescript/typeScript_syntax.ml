open Prelude
open Sig

module Pat = Dprle.Set
module rec StrobeImpl : (Strobe_sigs.STROBE_TYPS
                         with type extKind = TypeScriptImpl.kind
  with type extTyp = TypeScriptImpl.typ
  with type extBinding = TypeScriptImpl.binding
  with type pat = Pat.t) = Strobe_typ.Make (Pat) (TypeScriptImpl)
and TypeScriptImpl : (TypeScript_sigs.TYPESCRIPT_TYPS
               with type baseTyp = StrobeImpl.typ
  with type baseKind = StrobeImpl.kind
  with type baseBinding = StrobeImpl.binding) =
    TypeScript_types.Make (StrobeImpl)

module rec TypeScript : (TypeScript_sigs.TYPESCRIPT_ACTIONS
                     with type typ = TypeScriptImpl.typ
  with type kind = TypeScriptImpl.kind
  with type binding = TypeScriptImpl.binding
  with type env = TypeScriptImpl.env
  with type baseTyp = TypeScriptImpl.baseTyp
  with type baseKind = TypeScriptImpl.baseKind
  with type baseBinding = TypeScriptImpl.baseBinding) =
  TypeScript_types.MakeActions (Strobe) (TypeScriptImpl)
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
  Strobe_typ.MakeActions (Pat) (StrobeImpl) (TypeScript)

module StrobeMod = Strobe_typ.MakeModule (Pat) (Strobe) (TypeScript)
module TypeScriptMod = TypeScript_types.MakeModule (StrobeMod) (TypeScript) 


module rec TypeScript_kind : (TypeScript_sigs.TYPESCRIPT_KINDING
                             with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env)
  = TypeScript_kinding.Make (TypeScriptMod) (Strobe_kind)
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
  = Strobe_kinding.Make (StrobeMod) (TypeScript_kind)

module Exp = Typedjs_syntax.Exp (StrobeMod)

