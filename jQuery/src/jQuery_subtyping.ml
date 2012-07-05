open Prelude
open Sig
open Strobe_sigs
open JQuery_sigs


module MakeActions
  (StrobeSub : STROBE_SUBTYPING)
  (JQ : JQUERY_MODULE
   with type baseTyp = StrobeSub.typ
  with type baseKind = StrobeSub.kind
  with type baseBinding = StrobeSub.binding
  with type typ = StrobeSub.extTyp
  with type kind = StrobeSub.extKind
  with type binding = StrobeSub.extBinding
  with type env = StrobeSub.env)
  (Env : JQUERY_TYP_ENV
   with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type binding = JQ.binding
  with type env = JQ.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
  : (JQUERY_SUBTYPING
     with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type sigma = JQ.sigma
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type sel = JQ.sel
  with type env = JQ.env) =
struct
  include JQ
  open JQ
  open ListExt


  module SigmaPair = struct
    type s = STyps of typ * typ | SMults of multiplicity * multiplicity | SMultTyp of multiplicity * typ
    type t = env * s
    let compare = Pervasives.compare
  end
  module SPMap = Map.Make (SigmaPair)
  module SPMapExt = MapExt.Make (SigmaPair) (SPMap)

  (* returns an env containing only the (transitively) free variables in s *)
  let rec project s (env : env) =
    let union map1 map2 = IdMap.fold IdMap.add map1 map2 in
    let (free_t, free_m) = free_sigma_ids s in
    let rec helper id bindings acc =
      if not (IdSet.mem id free_t || IdSet.mem id free_m) then acc
      else 
        let trans = List.fold_left (fun acc bind -> match bind with
          | BStrobe (Strobe.BTermTyp t)
          | BStrobe (Strobe.BTypBound(t, _))
          | BStrobe (Strobe.BLabelTyp t) -> project (STyp (embed_t t)) env
          | BStrobe (Strobe.BEmbed b) -> helper id [b] acc
          | BMultBound(m, _) -> project (SMult m) env) acc bindings in
        union (IdMap.add id bindings acc) trans in
    IdMap.fold helper env IdMap.empty
  let project_mult_typ m t (env : env) = IdMap.fold IdMap.add (project (SMult m) env) (project (STyp t) env)
  let project_typs t1 t2 (env : env) = IdMap.fold IdMap.add (project (STyp t1) env) (project (STyp t2) env)
  let project_mults m1 m2 (env : env) = IdMap.fold IdMap.add (project (SMult m1) env) (project (SMult m2) env)


  let cache_hits = ref 0
  let cache_misses = ref 0

  let rec subtype_sigma lax (env : env) cache s1 s2 = 
    let open SigmaPair in
    match s1, s2 with
    | STyp t1, STyp t2 -> subtype_typ lax env cache t1 t2
    | SMult m1, SMult m2 -> subtype_mult lax env cache m1 m2
    (* SUPER-CRITICAL LAXITY RULE *)
    | SMult m1, STyp t2 -> 
      if lax then
        let (cache, ret) = subtype_mult lax env cache m1 (MZeroPlus (MPlain t2)) in
        (SPMap.add (project_mult_typ m1 t2 env, SMultTyp (m1, t2)) ret cache, ret)
      else
        (cache, false)
    (* ************************** *)
    | _ -> (cache, false)

  and subtype_typ lax (env : env) cache t1 t2 : (bool SPMap.t * bool) =
    let subtype_sigma = subtype_sigma lax in
    let subtype_typ = subtype_typ lax in
    let open SigmaPair in
    let (&&&) c thunk = if (snd c) then thunk (fst c) else c in
    let subtype_sigma_list c t1 t2 = c &&& (fun c -> subtype_sigma env c t1 t2) in
    let addToCache (cache, ret) = (SPMap.add (project_typs t1 t2 env, STyps (t1, t2)) ret cache, ret) in
    try incr cache_hits; (cache, SPMap.find (project_typs t1 t2 env, STyps (t1, t2)) cache)
    with Not_found -> begin decr cache_hits; incr cache_misses; addToCache (if t1 = t2 then (cache, true)
      else match t1, t2 with
      | TStrobe t1, TStrobe t2 -> cache, StrobeSub.subtype env t1 t2
      | TDom (_, t1, sel1), TDom (_, t2, sel2) ->
        subtype_typ env cache t1 t2 &&& (fun c -> (c, Css.is_subset IdMap.empty sel1 sel2))
      | TDom _, _ -> subtype_typ env cache t1 (TDom(None, t2, Css.all))
      | _, TDom _ -> subtype_typ env cache (TDom(None, t1, Css.all)) t2
      | TApp(t1, args1), TApp(t2, args2) ->
        if (List.length args1 <> List.length args2) then (cache, false)
        else List.fold_left2 subtype_sigma_list (cache, true) ((STyp t1)::args1) ((STyp t2)::args2)
      | TForall (_, x1, s1, t1), TForall (_, x2, s2, t2) -> 
        (* Kernel rule *)
        if not (equivalent_sigma env s1 s2) then cache, false
        else 
          let t2 = typ_typ_subst x2 (embed_t (Strobe.TId x1)) t2 in
          let env' = match s2 with
            | STyp t -> Env.bind_typ_id x1 t env
            | SMult m -> Env.bind_mult_id x1 m env in
          subtype_typ env' cache t1 t2
      | _ -> (cache, false))
    end
      
  and subtype_mult lax (env : env) cache m1 m2 = 
    let subtype_mult = subtype_mult lax env in
    let subtype_typ = subtype_typ lax env in (* ok for now because there are no MId binding forms in Mult *)
    let open SigmaPair in
    let addToCache (cache, ret) = (SPMap.add (project_mults m1 m2 env, SMults (m1, m2)) ret cache, ret) in
    try incr cache_hits; (cache, SPMap.find (project_mults m1 m2 env, SMults (m1, m2)) cache)
    with Not_found -> decr cache_hits; incr cache_misses; addToCache (match m1, m2 with
    | MId n1, t2 when t2 = MId n1 -> cache, true (* SA-Refl-TVar *)
    | MId n1, _ -> (* SA-Trans-TVar *)
      (try
         let m1 = Env.lookup_mult_id n1 env in
         subtype_mult cache m1 m2
       with Not_found -> cache, false)
    | MPlain t1, MPlain t2 -> subtype_typ cache t1 t2
    | MOne (MPlain t1), MOne (MPlain t2)
    | MOne (MPlain t1), MZeroOne (MPlain t2)
    | MOne (MPlain t1), MOnePlus (MPlain t2) -> subtype_typ cache t1 t2
    | MOne (MPlain _), MZero _ -> (cache, false)
    | MOne _, _ -> (cache, false) (* not canonical! *)
    | MZero _, MZero _
    | MZero _, MZeroOne _
    | MZero _, MZeroPlus _ -> (cache, true)
    | MZero _, _ -> (cache, false)
    | MZeroOne (MPlain t1), MZeroOne (MPlain t2) -> subtype_typ cache t1 t2
    | MZeroOne (MPlain _), MOne (MPlain _)
    | MZeroOne (MPlain _), MZero _
    | MZeroOne (MPlain _), MOnePlus (MPlain _) -> (cache, false)
    | MZeroOne _, _ -> (cache, false) (* not canonical! *)
    | MOnePlus (MPlain t1), MOnePlus (MPlain t2) -> subtype_typ cache t1 t2
    | MOnePlus (MPlain _), MZero _
    | MOnePlus (MPlain _), MOne _
    | MOnePlus (MPlain _), MZeroOne _ -> (cache, false)
    | MOnePlus _, _ -> (cache, false) (* not canonical! *)
    | MZeroPlus m1', MZero _ -> subtype_mult cache m1' m2
    | MZeroPlus _, MOne _ -> (cache, false)
    | MZeroPlus m1', MZeroOne m2' -> subtype_mult cache m1' (MZero m2')
    | MZeroPlus _, MOnePlus _ -> (cache, false)
    | MZeroPlus m1', MZeroPlus m2' -> subtype_mult cache m1' m2'
    | MZeroPlus _, _ -> (cache, false) (* not canonical! *)
    | MSum _, _
    | MPlain _, _ -> (cache, false) (* not canonical! *)
    )

  and cache : bool SPMap.t ref = ref SPMap.empty

  let print_cache lbl print_env =
    let open SigmaPair in
    let open Format in
    let open FormatExt in
    let cut fmt = Format.pp_print_cut fmt () in
    SPMapExt.p_map lbl cut
      (fun (env, sp) -> match sp with
      | STyps (t1, t2) -> 
        pair
          (label_braces "Env: " cut (print_env env))
          (label_pair "STyps" (JQ.Pretty.typ t1) (JQ.Pretty.typ t2))
      | SMults (m1, m2) -> 
        pair
          (label_braces "Env: " cut (print_env env))
          (label_pair "SMults" (JQ.Pretty.multiplicity m1) (JQ.Pretty.multiplicity m2))
      | SMultTyp (m1, t2) -> 
        pair
          (label_braces "Env: " cut (print_env env))
          (label_pair "SMultTyp" (JQ.Pretty.multiplicity m1) (JQ.Pretty.typ t2)))
      (fun b -> text (string_of_bool b))
      !cache

  (* SUBTYPING ONLY WORKS ON CANONICAL FORMS *)
  let subtype_sigma lax env s1 s2 =
    (let (c, r) = (subtype_sigma lax env !cache (canonical_sigma s1) (canonical_sigma s2))
     in cache := c; r)
  let subtype_typ lax env t1 t2 =
    (let (c, r) = (subtype_typ lax env !cache (canonical_type t1) (canonical_type t2))
     in cache := c; r)
  let subtype_mult lax env m1 m2 =
    (let (c, r) = (subtype_mult lax env !cache (canonical_multiplicity m1) (canonical_multiplicity m2))
     in cache := c; r)

  let subtype = subtype_typ true
end
