open Prelude
open Sig

module W = Typedjs_writtyp.WritTyp
module List = ListExt
module Pat = TypeScript_syntax.Pat
module StringMap = Map.Make (String)
module StringMapExt = MapExt.Make (String) (StringMap)

module type TYPESCRIPT_DESUGAR = sig
  include DESUGAR
  type kind
end

module Make
  (S : Strobe_sigs.STROBE_TYPS with type pat = Pat.t)
  (TypeScript : TypeScript_sigs.TYPESCRIPT_MODULE
   with type baseTyp = S.typ
  with type baseKind = S.kind
  with type typ = S.extTyp
  with type kind = S.extKind)
  : (TYPESCRIPT_DESUGAR 
     with type typ = TypeScript.typ
     with type writtyp = W.t
  with type kind = TypeScript.kind) =
struct
  type typ = TypeScript.typ
  type writtyp = W.t
  type kind = TypeScript.kind

  exception Typ_stx_error of string

  let error msg = 
    raise (Typ_stx_error msg)

  let is_star f = match f with
    | W.Star _ -> true
    | _ -> false

  let is_skull f = match f with
    | W.Skull _ -> true
    | _ -> false

  let is_absent f = match f with
    | W.Absent p -> true
    | _ -> false

  let pat_of f = match f with
    | W.Present (p, _) -> p
    | W.Inherited (p, _) -> p
    | W.Maybe (p, _) -> p
    | W.Absent p -> p
    | W.Skull p -> p
    | W.Star _ -> failwith "pat_of applied to Star _"

  let assert_overlap pat1 pat2 = match Pat.example (Pat.intersect pat1 pat2) with
    | None -> ()
    | Some str ->
      error (sprintf "%s and %s are overlapped. E.g.,\n%s\n is in both patterns." 
         (Pat.pretty pat1) (Pat.pretty pat2) str)

  let rec kind k =
    let open S in
    match k with
      | W.KStar -> KStar
      | W.KArrow (ks, k) -> KArrow (map kind ks, kind k)
      | _ -> failwith "TypeScriptDesugar: Unrecognized kind"

  let rec typ (writ_typ : W.t) : S.typ =
    let get_typ t = match t with
      | W.Typ t -> typ t
      | _ -> failwith (sprintf "TypeScriptDesugar: Got non-type in type application: %s" (W.sigma_of_typ t))
    in
    let open S in
    let opt_map f v = match v with None -> None | Some v -> Some (f v) in
    match writ_typ with
    | W.Str -> TRegex Pat.all
    | W.Prim p -> TPrim p
    | W.Bool -> TUnion (Some "Bool", TPrim "True", TPrim "False")
    | W.Union (t1, t2) -> TUnion (None, typ t1, typ t2)
    | W.Inter (t1, t2) -> TInter (None, typ t1, typ t2)
    | W.Arrow (None, args, var, r) -> TArrow (map typ args, opt_map typ var, typ r)
    | W.Arrow (Some this, args, var, r) -> TArrow ((typ this):: (map typ args), opt_map typ var, typ r)
    | W.This t -> TThis (typ t)
    | W.Object flds -> object_typ flds
    | W.With(t, flds) -> (match object_typ flds with 
      | TObject objflds -> TWith(typ t, objflds)
      | _ -> failwith "absurd")
    | W.Pat pat -> TRegex pat
    | W.Ref t -> TRef (None, typ t)
    | W.Source t -> TSource (None, typ t)
    | W.Top -> TTop
    | W.Bot -> TBot
    | W.Syn x -> TId x
    | W.TId x -> TId x
    | W.App (t1, t2s) -> TApp (typ t1, map get_typ t2s)
    | W.Forall (x, s, t) -> TForall (None, x, get_typ s, typ t)
    | W.Rec (x, t) -> TRec (None, x, typ t)
    | W.Lambda (args, t) ->
      let get_arg (id, k) = (id, kind k) in
      TLambda (None, map get_arg args, typ t)
    | W.Fix (x, k, t) -> TFix (None, x, kind k, typ t)

  and fld (writ_fld : W.f) : S.field =
    let open S in
    match writ_fld with
      | W.Present (pat, t) -> (pat, Present, typ t)
      | W.Maybe (pat, t) -> (pat, Maybe, typ t)
      | W.Inherited (pat, t) -> (pat, Inherited, typ t)
      | W.Absent pat -> error "fld applied to Absent"
      | W.Skull _ -> error "fld applied to Skull"
      | W.Star _ -> error "fld applied to Star"

  and object_typ (flds : W.f list) =
    let (flds_no_absents, absent_pat) = 
      let (absents, others) = List.partition is_absent flds in
      (others, 
       Pat.unions (List.map pat_of absents)) in
    let (flds_no_stars, absent_pat) =
      let (stars, others) = List.partition is_star flds_no_absents in
      match stars with
      | [] -> let skulls = List.filter is_skull others in
              begin match skulls with
              | [] -> (others, absent_pat)
              | _ -> error "BAD is nonsensical without *"
              end
      | [W.Star opt_star_typ] ->
        let star_pat =
          Pat.negate (Pat.unions (absent_pat::(map pat_of others))) in
        begin match opt_star_typ with
        | None -> (others, Pat.union star_pat absent_pat)
        | Some t -> ((W.Maybe (star_pat, t)) :: others, absent_pat)
        end
     | _ -> error "multiple stars (*) in an object type" in
    (* TODO(arjun): Why is this overlap check here? Can we do it at the top
       of the function? *)
    List.iter_pairs assert_overlap 
      (absent_pat :: (List.map pat_of flds_no_stars));
    let flds_no_skulls_stars = 
      List.filter (fun f -> not (is_skull f)) flds_no_stars in
    S.TObject (S.mk_obj_typ (map fld flds_no_skulls_stars) absent_pat)



  let desugar_typ (p : Pos.t) (wt : W.t) : typ =
    try TypeScript.embed_t (typ wt)
    with Typ_stx_error msg ->
      raise (Typ_stx_error (Pos.toString p ^ msg))
(*
  let typ (writ_typ : W.t) : TypeScript.typ =
    TypeScript.embed_t (S.TId "dummy-typescript-desugar-typ")

  let desugar_typ (p : Pos.t) (wt : W.t) : TypeScript.typ =
    try TypeScript.embed_t (TypeScript.extract_t (typ wt))
    with Typ_stx_error msg ->
      raise (Typ_stx_error (Pos.toString p ^ msg))
      *)
      
end 
