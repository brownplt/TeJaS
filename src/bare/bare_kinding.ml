open Prelude
open Sig
open Bare_sigs
open Strobe_sigs


module Make
  (Bare : BARE_MODULE)
  (StrobeKind : STROBE_KINDING
             with type typ = Bare.baseTyp
  with type kind = Bare.baseKind
  with type binding = Bare.baseBinding
  with type extTyp = Bare.typ
  with type extKind = Bare.kind
  with type extBinding = Bare.binding
  with type env = Bare.env) =
struct
  include Bare
  open Bare
      
  let list_prims = StrobeKind.list_prims
  let new_prim_typ = StrobeKind.new_prim_typ

  let kind_check_typ (env : env) (recIds : id list) (typ : typ) : kind = 
    match typ with
    | TStrobe t -> embed_k (StrobeKind.kind_check env recIds t)

  let kind_check = kind_check_typ

end
