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

  let kind_mismatch typ calculated_kind expected_kind = 
    raise 
      (Strobe.Kind_error 
         (sprintf "Expected kind %s, but got kind %s for type:\n%s"
            (string_of_kind expected_kind)
            (string_of_kind calculated_kind)
            (string_of_typ typ)))

  let rec kind_check_typ (env : env) (recIds : id list) (typ : typ) : kind = 
    match typ with
    | TStrobe t -> embed_k (StrobeKind.kind_check env recIds t)
    | TArrow (args, varargs, ret) ->
      let assert_kind t = match extract_k (kind_check_typ env recIds t) with
        | Strobe.KStar -> ()
        | k -> kind_mismatch t (embed_k k) (embed_k Strobe.KStar) in
      List.iter assert_kind (ret :: args);
      (match varargs with None -> () | Some v -> assert_kind v);
      embed_k Strobe.KStar


  let kind_check = kind_check_typ

end
