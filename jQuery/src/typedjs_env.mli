open Prelude
open Sig
open Strobe_sigs

module Make : 
  functor (Strobe : STROBE_MODULE) ->
    functor (StrobeKinding : STROBE_KINDING
             with type typ = Strobe.typ
  with type kind = Strobe.kind
  with type binding = Strobe.binding
  with type extTyp = Strobe.extTyp
  with type extKind = Strobe.extKind
  with type extBinding = Strobe.extBinding) ->
      functor (Desugar : Typedjs_desugar.DESUGAR with type typ = Strobe.extTyp with type kind = Strobe.extKind) ->
        (TYP_ENV
         with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
        
