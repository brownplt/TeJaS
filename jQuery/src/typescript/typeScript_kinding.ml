open Prelude
open Sig
open TypeScript_sigs
open Strobe_sigs


module Make
  (TypeScript : TYPESCRIPT_MODULE)
  (StrobeKind : STROBE_KINDING
             with type typ = TypeScript.baseTyp
  with type kind = TypeScript.baseKind
  with type binding = TypeScript.baseBinding
  with type extTyp = TypeScript.typ
  with type extKind = TypeScript.kind
  with type extBinding = TypeScript.binding
  with type env = TypeScript.env) =
struct
  include TypeScript
  open TypeScript
      
  let list_prims = StrobeKind.list_prims
  let new_prim_typ = StrobeKind.new_prim_typ

  let kind_check_typ (env : env) (recIds : id list) (typ : typ) : kind = 
    match typ with
    | TStrobe t -> embed_k (StrobeKind.kind_check env recIds t)

  let kind_check = kind_check_typ

end
