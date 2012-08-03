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
        IdMap.add id (List.filter (fun b -> match b with BStrobe (Strobe.BTermTyp _) -> false | _ -> true)
                        (IdMap.find id env)) acc
      with Not_found -> ((* Strobe.traceMsg "Couldn't find %s" id; *) acc)) set map in
    let free_ids = add_id_bindings free_t (add_id_bindings free_m IdMap.empty) in
    (* let s = match s with *)
    (*   | SMult m -> string_of_mult m *)
    (*   | STyp t -> string_of_typ t in *)
    (* Strobe.traceMsg "Free mult ids for %s are: {%s}" s (String.concat "," (IdSetExt.to_list free_m)); *)
    (* Strobe.traceMsg "Free typ ids for %s are: {%s}" s (String.concat "," (IdSetExt.to_list free_t)); *)
    let rec helper free_ids acc =
    (*   let s = (String.concat "," (IdMapExt.keys free_ids)) in *)
    (*   Strobe.trace "Ids being checked: " s (fun _ -> true) (fun () -> helper' free_ids acc) *)
    (* and helper' free_ids acc = *)
      if IdMap.cardinal free_ids = 0 then acc else
        let acc' = IdMap.fold IdMap.add free_ids acc in
        let free_ids' = IdMap.fold (fun id bs acc -> 
          let free_ids = List.fold_left (fun ids b -> match unwrap_b b with
            | BStrobe (Strobe.BTermTyp t) -> ids
            | BStrobe (Strobe.BTypBound(t, _))
            | BStrobe (Strobe.BLabelTyp t) -> 
              let (free_t, free_m) = JQ.free_sigma_ids (STyp (embed_t t)) in
              let free_ids = IdSet.union free_t free_m in
              (* Strobe.traceMsg "Free typ mult_ids for %s are: {%s}" (string_of_typ (embed_t t)) *)
              (*   (String.concat "," (IdSetExt.to_list free_m)); *)
              (* Strobe.traceMsg "Free typ typ_ids for %s are: {%s}" (string_of_typ (embed_t t)) *)
              (*   (String.concat "," (IdSetExt.to_list free_t)); *)
              IdSet.union ids free_ids
            | BStrobe (Strobe.BEmbed _) -> ids
            | BStrobe (Strobe.BTyvar _) -> ids
            | BMultBound(m, _) -> 
              let (free_t, free_m) = JQ.free_sigma_ids (SMult m) in 
              let free_ids = IdSet.union free_t free_m in
              (* Strobe.traceMsg "New mult free_ids for %s are %s" (string_of_mult m) *)
              (*   (String.concat "," (IdSetExt.to_list free_ids)); *)
              IdSet.union ids free_ids)
            IdSet.empty bs in
          add_id_bindings free_ids acc) free_ids acc' in
        let free_ids' = IdMap.filter (fun id _ -> not (IdMap.mem id acc)) free_ids' in
        helper free_ids' acc' in
    (* Strobe.trace "Projecting free vars of " s (fun _ -> true) (fun () -> helper free_ids IdMap.empty) *)
    helper free_ids IdMap.empty
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
    | STyp t, SMult m -> (cache, false)

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
      else match unwrap_t t1, unwrap_t t2 with
      (* Case for handling two-arg jQ types *)
      | ((TApp (TStrobe (Strobe.TFix(Some "jQ", "jq", _,_)), [m1; p1])) (* as jq1 *)),
        ((TApp (TStrobe (Strobe.TFix(Some "jQ", "jq", _,_)), [m2; p2])) (* as jq2 *)) ->
        List.fold_left2 subtype_sigma_list (cache, true) [m1;p1] [m2;p2]
      (* convenience for AnyJQ *)
      | t1, TStrobe ((Strobe.TId "AnyJQ") as anyJQ) ->
        subtype_typ env cache t1 (embed_t (Strobe.expose env anyJQ))
      | ((TApp (TStrobe (Strobe.TFix(Some "jQ", "jq", _,_)), [m1; p1])) as jq1),
        TForall (Some "AnyJQ", x, _, t) ->
        let t2 = (replace_name None (sig_typ_subst x p1 t)) in
        subtype_typ env cache jq1 t2
      (* default cases *)
      | t1, t2 ->
        let simpl_t1 = simpl_typ env t1 in
        let simpl_t2 = simpl_typ env t2 in
        let env' = project_typs simpl_t1 simpl_t2 env in
        try (cache, SPMap.find (env', STyps (simpl_t1, simpl_t2)) cache)
        with Not_found ->
          (* Strobe.traceMsg "JQUERY ASSUMING %s <: %s, checking for consistency" (string_of_typ t1) (string_of_typ t2); *)
          let cache = SPMap.add (env', STyps (t1, t2)) true cache in
          let (|||) c thunk = if (snd c) then c else thunk (fst c) in
          let (&&&) c thunk = if (snd c) then thunk (fst c) else c in
          match unwrap_t simpl_t1, unwrap_t simpl_t2 with
          | TStrobe (Strobe.TUnion(_, t11, t12)), t2 -> (* order matters -- left side must be split first! *)
            subtype_typ env cache (embed_t t11) t2 &&& (fun c -> subtype_typ env c (embed_t t12) t2)
          | t1, TStrobe (Strobe.TUnion(_, t21, t22)) ->
            subtype_typ env cache t1 (embed_t t21) ||| (fun c -> subtype_typ env c t1 (embed_t t22))
          | t1, TStrobe (Strobe.TInter(_, t21, t22)) -> (* order matters -- right side must be split first! *)
            subtype_typ env cache t1 (embed_t t21) &&& (fun c -> subtype_typ env c t1 (embed_t t22))
          | TStrobe (Strobe.TInter(_, t11, t12)), t2 ->
            subtype_typ env cache (TStrobe t11) t2 ||| (fun c -> subtype_typ env c (TStrobe t12) t2)

          | TStrobe t1, TStrobe t2 -> 
            tc_cache := cache; (* checkpoint state *)
            cache, StrobeSub.subtype env t1 t2
          | TDom (_, t1, sel1), TDom (_, t2, sel2) ->
            subtype_typ env cache t1 t2 &&& (fun c -> (c, Css.is_subset IdMap.empty sel1 sel2))
          | TDom _, _ -> subtype_typ env cache t1 (Env.expose_tdoms env (TDom(None, t2, Css.all)))
          | _, TDom _ -> subtype_typ env cache (Env.expose_tdoms env (TDom(None, t1, Css.all))) t2
          | TApp _, TApp _ -> cache, false
          (* UNSOUND: Type constructor might not be covariant in its arguments *)
          (* | TApp(t1, args1), TApp(t2, args2) -> *)
          (*   if (List.length args1 <> List.length args2) then (cache, false) *)
          (*   else List.fold_left2 subtype_sigma_list (cache, true) ((STyp t1)::args1) ((STyp t2)::args2) *)
          | TForall (_, x1, s1, t1), TForall (_, x2, s2, t2) -> 
            (* Kernel rule *)
            if not (equivalent_sigma env s1 s2) then cache, false
            else 
              let t2 = canonical_type (typ_typ_subst x2 (embed_t (Strobe.TId x1)) t2) in
              let env' = match s2 with
                | STyp t -> Env.bind_typ_id x1 t env
                | SMult m -> Env.bind_mult_id x1 m env in
              subtype_typ env' cache t1 t2
          | _ -> (cache, false))
    end
      
  and subtype_mult lax env cache m1 m2 =
    Strobe.trace "JQUERY_subtype_mult" (string_of_mult m1 ^ " <?: " ^ string_of_mult m2) snd2 (fun () -> subtype_mult' lax env cache m1 m2)
  and subtype_mult' lax (env : env) cache m1 m2 = 
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
    | MOne (MPlain t1), MOnePlus (MPlain t2)
    | MOne (MPlain t1), MZeroPlus (MPlain t2) -> subtype_typ cache t1 t2
    | MOne (MPlain _), MZero _ -> (cache, false)
    | MOne _, _ -> (cache, false) (* not canonical! *)
    | MZero (MPlain t1), MZero (MPlain t2)
    | MZero (MPlain t1), MZeroOne (MPlain t2)
    | MZero (MPlain t1), MZeroPlus (MPlain t2) -> subtype_typ cache t1 t2
    | MZero _, _ -> (cache, false)
    | MZeroOne (MPlain t1), MZeroOne (MPlain t2)
    | MZeroOne (MPlain t1), MZeroPlus (MPlain t2) -> subtype_typ cache t1 t2
    | MZeroOne (MPlain _), MOne (MPlain _)
    | MZeroOne (MPlain _), MZero _
    | MZeroOne (MPlain _), MOnePlus (MPlain _) -> (cache, false)
    | MZeroOne _, _ -> (cache, false) (* not canonical! *)
    | MOnePlus (MPlain t1), MOnePlus (MPlain t2)
    | MOnePlus (MPlain t1), MZeroPlus (MPlain t2) -> subtype_typ cache t1 t2
    | MOnePlus (MPlain _), MZero _
    | MOnePlus (MPlain _), MOne _
    | MOnePlus (MPlain _), MZeroOne _ -> (cache, false)
    | MOnePlus _, _ -> (cache, false) (* not canonical! *)
    | MZeroPlus (MPlain t1), MZeroPlus (MPlain t2) -> subtype_typ cache t1 t2
    | MZeroPlus (MPlain _), _ -> (cache, false)
    | MZeroPlus _, _ -> (cache, false) (* not canonical! *)
    | MSum _, _
    | MPlain _, _ -> (cache, false) (* not canonical! *)
    )

  and tc_cache : bool SPMap.t ref = ref SPMap.empty

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
          (squish[text "STyps"; (pair (JQ.Pretty.typ t1) (JQ.Pretty.typ t2))])
      | SMults (m1, m2) -> 
        pair
          (label_braces "Env: " cut [Env.print_env env])
          (squish[text "SMults"; (pair (JQ.Pretty.multiplicity m1) (JQ.Pretty.multiplicity m2))])
      | SMultTyp (m1, t2) -> 
        pair
          (label_braces "Env: " cut [Env.print_env env])
          (squish[text "SMultTyp"; (pair (JQ.Pretty.multiplicity m1) (JQ.Pretty.typ t2))]))
      (fun b -> text (string_of_bool b))
      !tc_cache
      

  (* SUBTYPING ONLY WORKS ON CANONICAL FORMS *)
  let subtype_sigma lax env s1 s2 =
    (let (c, r) = (subtype_sigma lax env !tc_cache (canonical_sigma s1) (canonical_sigma s2))
     in tc_cache := c; r)
  let subtype_typ lax env t1 t2 =
    (* Strobe.traceMsg "attempting to resolve t1: %s | t2: %s"  *)
    (*   (string_of_typ t1) (string_of_typ t2); *)
    let t1' = (Env.resolve_special_functions env !Env.senv 
             (Env.expose_tdoms env (canonical_type t1))) in
    let t2' = (Env.resolve_special_functions env !Env.senv 
             (Env.expose_tdoms env (canonical_type t2))) in
    (* Strobe.traceMsg "resolved t1: %s | t2: %s" *)
    (*   (string_of_typ t1') (string_of_typ t2'); *)
    let (c, r) = 
       (subtype_typ lax env !tc_cache t1' t2')

     in tc_cache := c; r
  let subtype_mult lax env m1 m2 =
    (let (c, r) = (subtype_mult lax env !tc_cache (canonical_multiplicity m1) (canonical_multiplicity m2))
     in tc_cache := c; r)

  let subtype = subtype_typ true
end
