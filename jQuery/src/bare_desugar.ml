open Prelude
open Sig

module W = Typedjs_writtyp.WritTyp
module List = ListExt
module Pat = Bare_syntax.Pat
module StringMap = Map.Make (String)
module StringMapExt = MapExt.Make (String) (StringMap)

module type BARE_DESUGAR = sig
  include DESUGAR
  type kind
end

module Make
  (S : Strobe_sigs.STROBE_TYPS with type pat = Pat.t)
  (Bare : Bare_sigs.BARE_MODULE
   with type baseTyp = S.typ
  with type baseKind = S.kind
  with type typ = S.extTyp
  with type kind = S.extKind)
  : (BARE_DESUGAR 
     with type typ = Bare.typ
     with type writtyp = W.t
  with type kind = Bare.kind) =
struct
  type typ = Bare.typ
  type writtyp = W.t
  type kind = Bare.kind

  exception Typ_stx_error of string

  let typ (writ_typ : W.t) : Bare.typ =
    Bare.embed_t (S.TId "dummy-bare-desugar-typ")

  let desugar_typ (p : Pos.t) (wt : W.t) : Bare.typ =
    try Bare.embed_t (Bare.extract_t (typ wt))
    with Typ_stx_error msg ->
      raise (Typ_stx_error (Pos.toString p ^ msg))
      
end 
