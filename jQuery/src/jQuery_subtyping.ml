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
    let (free_t, free_m) = free_sigma_ids s in
    let add_id_bindings set map = IdSet.fold (fun id acc -> 
      try
        IdMap.add id (IdMap.find id env) acc
      with Not_found -> (Printf.eprintf "Couldn't find %s\n" id; acc)) set map in
    let free_ids = add_id_bindings free_t (add_id_bindings free_m IdMap.empty) in
    let s = match s with
      | SMult m -> string_of_mult m
      | STyp t -> string_of_typ t in
    let rec helper free_ids acc =
      if IdMap.cardinal free_ids = 0 then acc else
        let acc' = IdMap.fold IdMap.add free_ids acc in
        let free_ids' = IdMap.fold (fun id bs acc -> 
          let free_ids = List.fold_left (fun ids b -> match unwrap_b b with
            | BStrobe (Strobe.BTermTyp t)
            | BStrobe (Strobe.BTypBound(t, _))
            | BStrobe (Strobe.BLabelTyp t) -> 
              let free_ids = JQ.free_ids (embed_t t) in
              (* Printf.eprintf "New free_ids for %s are %s\n" (string_of_typ (embed_t t)) *)
              (*   (String.concat "," (IdSetExt.to_list free_ids)); *)
              IdSet.union ids free_ids
            | BStrobe (Strobe.BEmbed _) -> ids
            | BStrobe (Strobe.BTyvar _) -> ids
            | BMultBound(m, _) -> 
              let (free_t, free_m) = JQ.free_sigma_ids (SMult m) in 
              let free_ids = IdSet.union free_t free_m in
              (* Printf.eprintf "New free_ids for %s are %s\n" (string_of_mult m) *)
              (*   (String.concat "," (IdSetExt.to_list free_ids)); *)
              IdSet.union ids free_ids)
            IdSet.empty bs in
          add_id_bindings free_ids acc) free_ids acc' in
        let free_ids' = IdMap.filter (fun id _ -> IdMap.mem id acc) free_ids' in
        helper free_ids' acc' in
    Strobe.trace "Projecting free vars of " s (fun _ -> true) (fun () -> helper free_ids IdMap.empty)
  let project_mult_typ m t (env : env) = IdMap.fold IdMap.add (project (SMult m) env) (project (STyp t) env)
  let project_typs t1 t2 (env : env) = IdMap.fold IdMap.add (project (STyp t1) env) (project (STyp t2) env)
  let project_mults m1 m2 (env : env) = IdMap.fold IdMap.add (project (SMult m1) env) (project (SMult m2) env)


  let cache_hits = ref 0
  let cache_misses = ref 0
  let num_cache_hits () = !cache_hits
  let num_cache_misses () = !cache_misses

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

  and subtype_typ lax env cache s t =
    Strobe.trace "JQUERY_subtype_typ" (string_of_typ s ^ " <?: " ^ string_of_typ t) snd2 (fun () -> subtype_typ' lax env cache s t)
  and subtype_typ' lax (env : env) cache t1 t2 : (bool SPMap.t * bool) =
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

  let print_cache lbl =
    let open SigmaPair in
    let open Format in
    let open FormatExt in
    let cut fmt = Format.pp_print_cut fmt () in
    SPMapExt.p_map lbl cut
      (fun (env, sp) -> match sp with
      | STyps (t1, t2) -> 
        pair
          (label_braces "Env: " cut [Env.print_env env])
          (label_pair "STyps" (JQ.Pretty.typ t1) (JQ.Pretty.typ t2))
      | SMults (m1, m2) -> 
        pair
          (label_braces "Env: " cut [Env.print_env env])
          (label_pair "SMults" (JQ.Pretty.multiplicity m1) (JQ.Pretty.multiplicity m2))
      | SMultTyp (m1, t2) -> 
        pair
          (label_braces "Env: " cut [Env.print_env env])
          (label_pair "SMultTyp" (JQ.Pretty.multiplicity m1) (JQ.Pretty.typ t2)))
      (fun b -> text (string_of_bool b))
      !cache

      
  let rec resolve_special_functions (env : env) (senv : Env.structureEnv) (t : typ) =
    let rec extract_mult m = match m with
      | MPlain t -> (t, fun m -> m)
      | MOne m ->
        let (t, m) = extract_mult m in
        (t, fun t -> MOne (m t))
      | MZero m ->
        let (t, m) = extract_mult m in
        (t, fun t -> MZero (m t))
      | MOnePlus m ->
        let (t, m) = extract_mult m in
        (t, fun t -> MOnePlus (m t))
      | MZeroOne m ->
        let (t, m) = extract_mult m in
        (t, fun t -> MZeroOne (m t))
      | MZeroPlus m ->
        let (t, m) = extract_mult m in
        (t, fun t -> MZeroPlus (m t))
      | MId m -> 
        failwith ("can't handle MId(" ^ m ^ ") here")
      | MSum _ -> failwith "can't handle MSums here" in
    let rec resolve_sigma s = match s with
      | STyp t -> STyp (rjq t)
      | SMult m -> SMult (resolve_mult m) 
    and resolve_mult m =
      let rm = resolve_mult in
      match m with
      | MPlain t -> MPlain (rjq t)
      | MId _ -> m
      | MZero m-> MZero (rm m)
      | MOne m -> MOne (rm m)
      | MZeroOne m -> MZeroOne (rm m)
      | MOnePlus m -> MOnePlus (rm m)
      | MZeroPlus m -> MZeroPlus (rm m)
      | MSum (m1, m2) -> MSum (rm m1, rm m2)
    and  rjq t = match t with
      | TForall (s,id,sigma,t) -> TForall(s,id,resolve_sigma sigma, rjq t)
      | TLambda (s,iks,t) -> TLambda(s,iks,rjq t)
      | TApp(TStrobe (Strobe.TPrim "childrenOf"), [STyp t]) ->
        failwith "childrenOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "parentOf"), [STyp t]) ->
        failwith "parentOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "prevsibOf"), [STyp t]) ->
        failwith "prevsibOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "nextsibOf"), [STyp t]) ->
        failwith "nextsibOf at outermost level"
      | TApp(t, args) ->
        TApp(rjq t, List.map (fun s -> match s with
        | SMult m -> begin match extract_mult m with
          | TApp(TStrobe (Strobe.TPrim "childrenOf"), [STyp t]), m ->
            SMult (canonical_multiplicity (m (Env.children_of senv (rjq t))))
          | TApp(TStrobe (Strobe.TPrim "childrenOf"), _), _ ->
            failwith "childrenOf not called with a single type argument"
          | TApp(TStrobe (Strobe.TPrim "parentOf"), [STyp t]), m ->
            SMult (canonical_multiplicity (m (Env.parent_of senv (rjq t))))
          | TApp(TStrobe (Strobe.TPrim "parentOf"), _), _ ->
            failwith "parentOf not called with a single type argument"
          | TApp(TStrobe (Strobe.TPrim "prevsibOf"), [STyp t]), m ->
            SMult (canonical_multiplicity (m (Env.prevsib_of senv (rjq t))))
          | TApp(TStrobe (Strobe.TPrim "prevsibOf"), _), _ ->
            failwith "prevsibOf not called with a single type argument"
          | TApp(TStrobe (Strobe.TPrim "nextsibOf"), [STyp t]), m ->
            SMult (canonical_multiplicity (m (Env.nextsib_of senv (rjq t))))
          | TApp(TStrobe (Strobe.TPrim "nextsibOf"), _), _ ->
            failwith "nextsibOf not called with a single type argument"
          | _, _ -> SMult m
        end
        | STyp _ -> s) args)
      | TDom (s, t, sel) -> TDom (s, rjq t, sel)
      | TStrobe t -> TStrobe (rs t)
    and rs t = 
      let rs_obj o = Strobe.mk_obj_typ 
        (List.map (third3 rs) (Strobe.fields o)) 
        (Strobe.absent_pat o) in
      match t with 
      | Strobe.TPrim s -> t
      | Strobe.TUnion (s,t1,t2) -> Strobe.TUnion(s, rs t1, rs t2)
      | Strobe.TInter (s,t1,t2) -> Strobe.TInter(s, rs t1, rs t2)
      | Strobe.TArrow (ts,t1,t2) ->
        Strobe.TArrow(List.map rs ts,
                      (match t1 with None -> None | Some t -> Some (rs t)),
                      rs t2)
      | Strobe.TThis t -> Strobe.TThis (rs t)
      | Strobe.TObject o -> Strobe.TObject (rs_obj o)
      | Strobe.TWith (t, o) -> Strobe.TWith (rs t, rs_obj o)
      | Strobe.TRegex _ -> t
      | Strobe.TRef (s, t) -> Strobe.TRef (s, rs t)
      | Strobe.TSource (s, t) -> Strobe.TSource (s, rs t)
      | Strobe.TSink (s, t) -> Strobe.TSink (s, rs t)
      | Strobe.TTop -> Strobe.TTop
      | Strobe.TBot -> Strobe.TBot
      | Strobe.TForall (s,id,t1,t2) -> Strobe.TForall(s,id,rs t1, rs t2)
      | Strobe.TId id -> t
      | Strobe.TRec (s,id,t) -> Strobe.TRec (s, id, rs t)
      | Strobe.TLambda (s, iks, t) -> Strobe.TLambda (s, iks, rs t)
      | Strobe.TApp (t, ts) -> Strobe.TApp (rs t, (List.map rs ts))
      | Strobe.TFix (s, id, k, t) -> Strobe.TFix (s, id, k, rs t)
      | Strobe.TUninit tor -> 
        Strobe.TUninit (match !tor with Some t -> ref (Some (rs t)) | _ -> tor)
      | Strobe.TEmbed t -> Strobe.TEmbed (rjq t) in
    rjq t
      

  (* SUBTYPING ONLY WORKS ON CANONICAL FORMS *)
  let subtype_sigma lax env s1 s2 =
    (let (c, r) = (subtype_sigma lax env !cache (canonical_sigma s1) (canonical_sigma s2))
     in cache := c; r)
  let subtype_typ lax env t1 t2 =
    let (c, r) = 
       (subtype_typ lax env !cache
          (resolve_special_functions env !Env.senv 
             (Env.expose_tdoms env (canonical_type t1)))
          (resolve_special_functions env !Env.senv 
             (Env.expose_tdoms env (canonical_type t2))))
     in cache := c; r
  let subtype_mult lax env m1 m2 =
    (let (c, r) = (subtype_mult lax env !cache (canonical_multiplicity m1) (canonical_multiplicity m2))
     in cache := c; r)

  let subtype = subtype_typ true
end
