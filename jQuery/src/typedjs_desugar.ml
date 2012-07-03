open Prelude

module W = Typedjs_writtyp.WritTyp
module List = ListExt
module Pat = JQuery_syntax.Pat

module type DESUGAR = sig
  type typ
  type kind
  val desugar_typ : Pos.t -> W.t -> typ
end

module Make
  (S : Strobe_sigs.STROBE_TYPS with type pat = Pat.t)
  (JQ : JQuery_sigs.JQUERY_TYPS
   with type baseTyp = S.typ
  with type baseKind = S.kind
  with type typ = S.extTyp
  with type kind = S.extKind)
  : (DESUGAR 
     with type typ = JQ.typ
  with type kind = JQ.kind) =
struct
  type typ = JQ.typ
  type kind = JQ.kind
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

  let rec typ (writ_typ : W.t) : JQ.typ =
    match writ_typ with
    | W.Str -> JQ.TStrobe (S.TRegex Pat.all)
    | W.Prim p -> JQ.TStrobe (S.TPrim p)
    | W.Bool -> JQ.TStrobe (S.TUnion (Some "Bool", S.TPrim "True", S.TPrim "False"))
    | W.Union (t1, t2) -> JQ.TStrobe (S.TUnion (None, embed_typ t1, embed_typ t2))
    | W.Inter (t1, t2) -> JQ.TStrobe (S.TInter (None, embed_typ t1, embed_typ t2))
    | W.Arrow (None, args, var, r) -> JQ.TStrobe (S.TArrow ((* None,  *)map embed_typ args, opt_map embed_typ var, embed_typ r))
    | W.Arrow (Some this, args, var, r) -> JQ.TStrobe (S.TArrow ((* None, *) (embed_typ this):: (map embed_typ args), opt_map embed_typ var, embed_typ r))
    | W.This t -> JQ.TStrobe (S.TThis (embed_typ t))
    | W.Object flds -> JQ.TStrobe (object_typ flds)
    | W.With(t, flds) -> (match object_typ flds with
      | S.TObject objflds -> JQ.TStrobe (S.TWith(embed_typ t, objflds))
      | _ -> failwith "absurd")
    | W.Pat pat -> JQ.TStrobe (S.TRegex pat)
    | W.Ref t -> JQ.TStrobe (S.TRef (None, embed_typ t))
    | W.Source t -> JQ.TStrobe (S.TSource (None, embed_typ t))
    | W.Top -> JQ.TStrobe (S.TTop)
    | W.Bot -> JQ.TStrobe (S.TBot)
    | W.Syn x -> JQ.TStrobe (S.TId x)
    | W.TId x -> JQ.TStrobe (S.TId x)
    | W.App (t1, t2s) -> JQ.TApp (typ t1, map sigma t2s)
    | W.Forall (x, s, t) -> JQ.TForall (None, x, sigma s, typ t)
    | W.Rec (x, t) -> JQ.TStrobe (S.TRec (None, x, embed_typ t))
    | W.Lambda (args, t) -> JQ.TStrobe (S.TLambda (None, map id_kind args, embed_typ t))
    | W.Fix (x, k, t) -> let (x, k) = id_kind (x, k) in JQ.TStrobe (S.TFix (None, x, k, embed_typ t))

  and opt_map f v = match v with None -> None | Some v -> Some (f v)
  and embed_typ t = S.TEmbed (typ t)

  and id_kind (id, k) = 
    let rec helper k = match k with
      | W.KStar -> S.KStar
      | W.KArrow (args, ret) -> S.KArrow (map helper args, helper ret)
      | W.KMult m -> match helper m with
        | S.KEmbed m -> S.KEmbed (JQ.KMult m)
        | m -> S.KEmbed (JQ.KMult (JQ.KStrobe m))
    in (id, helper k)

  and sigma (writ_sig : W.s) : JQ.sigma = match writ_sig with 
    | W.Mult m -> JQ.SMult (mult m)
    | W.Typ t -> JQ.STyp (typ t)

  and mult (writ_mult : W.m) : JQ.multiplicity =
    match writ_mult with
    | W.Plain t -> JQ.MPlain (typ t)
    | W.MId id -> JQ.MId id
    | W.One m -> JQ.MOne (mult m)
    | W.Zero m -> JQ.MZero (mult m)
    | W.ZeroOne m -> JQ.MZeroOne (mult m)
    | W.OnePlus m -> JQ.MOnePlus (mult m)
    | W.ZeroPlus m -> JQ.MZeroPlus (mult m)
    | W.Sum (m1, m2) -> JQ.MSum(mult m1, mult m2)

  and fld (writ_fld : W.f) : S.field = match writ_fld with
    | W.Present (pat, t) -> (pat, S.Present, embed_typ t)
    | W.Maybe (pat, t) -> (pat, S.Maybe, embed_typ t)
    | W.Inherited (pat, t) -> (pat, S.Inherited, embed_typ t)
    | W.Absent pat -> error "fld applied to Absent"
    | W.Skull _ -> error "fld applied to Skull"
    | W.Star _ -> error "fld applied to Star"

  and object_typ (flds : W.f list) : S.typ =
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



  let desugar_typ (p : Pos.t) (wt : W.t) : JQ.typ =
    try typ wt
    with Typ_stx_error msg ->
      raise (Typ_stx_error (Pos.toString p ^ msg))
end
