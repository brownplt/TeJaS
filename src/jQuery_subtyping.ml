open Prelude
open JQuery_syntax
open TypImpl
open ListExt



module SigmaPair = struct
  type s = STyps of typ * typ | SMults of multiplicity * multiplicity | SMultTyp of multiplicity * typ
  type t = env * s
  let compare = Pervasives.compare
end
module SPMap = Map.Make (SigmaPair)
module SPMapExt = MapExt.Make (SigmaPair) (SPMap)

let rec expose_typ env t = match t with
  | TId x -> 
    (try (match IdMap.find x env with BTypBound (t, _) -> expose_typ env t | _ -> None)
     with Not_found -> None)
  | t -> Some t

(* returns an env containing only the (transitively) free variables in s *)
let rec project s env =
  let (free_t, free_m) = free_sigma_ids s in
  IdMap.fold (fun id bind acc ->
    if not (IdSet.mem id free_t || IdSet.mem id free_m) then acc
    else 
      let trans = match bind with
        | BTermTyp(t, _) -> project (STyp t) env
        | BTypBound(t, _) -> project (STyp t) env
        | BMultBound(m, _) -> project (SMult m) env in
      IdMap.fold IdMap.add trans acc) env IdMap.empty
let project_mult_typ m t env = project (SMult m) (project (STyp t) env)
let project_typs t1 t2 env = project (STyp t1) (project (STyp t2) env)
let project_mults m1 m2 env = project (SMult m1) (project (SMult m2) env)


let pat_env (env : env) : pat IdMap.t =
  let select_pat_bound (x, t) = match t with
    | BTermTyp(TRegex p, _) -> Some (x, p)
    | _ -> None in
  List.fold_right (fun (x,p) env -> IdMap.add x p env)
    (filter_map select_pat_bound (IdMap.bindings env))
    IdMap.empty

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

and subtype_typ lax env cache t1 t2 : (bool SPMap.t * bool) =
  let subtype_sigma = subtype_sigma lax in
  let subtype_typ = subtype_typ lax in
  let open SigmaPair in
  let (|||) c thunk = if (snd c) then c else thunk (fst c) in
  let (&&&) c thunk = if (snd c) then thunk (fst c) else c in
  let subtype_typ_list c t1 t2 = c &&& (fun c -> subtype_typ env c t1 t2) in
  let subtype_sigma_list c t1 t2 = c &&& (fun c -> subtype_sigma env c t1 t2) in
  let addToCache (cache, ret) = (SPMap.add (project_typs t1 t2 env, STyps (t1, t2)) ret cache, ret) in
  try (cache, SPMap.find (project_typs t1 t2 env, STyps (t1, t2)) cache)
  with Not_found -> begin addToCache (if t1 = t2 then (cache, true)
    else match t1, t2 with
    | _, TTop
    | TBot, _ -> (cache, true)
    | TRegex pat1, TRegex pat2 ->
      (cache, P.is_subset (pat_env env) pat1 pat2)
    | TPrim p1, TPrim p2 -> (cache, p1 = p2)
    | TId n1, t2 when t2 = TId n1 -> cache, true (* SA-Refl-TVar *)
    | TId n1, _ -> (* SA-Trans-TVar *)
      (try
         (match IdMap.find n1 env with 
         | BTypBound (t1, _) -> subtype_typ env cache t1 t2
         | _ -> cache, false)
       with Not_found -> cache, false)
    | TUnion(_, t11, t12), t2 -> (* order matters -- left side must be split first! *)
      subtype_typ env cache t11 t2 &&& (fun c -> subtype_typ env c t12 t2)
    | t1, TUnion(_, t21, t22) ->
      subtype_typ env cache t1 t21 ||| (fun c -> subtype_typ env c t1 t22)
    | t1, TInter(_, t21, t22) -> (* order matters -- right side must be split first! *)
      subtype_typ env cache t1 t21 &&& (fun c -> subtype_typ env c t1 t22)
    | TInter(_, t11, t12), t2 ->
      subtype_typ env cache t11 t2 ||| (fun c -> subtype_typ env c t12 t2)
    | TApp(t1, args1), TApp(t2, args2) ->
      if (List.length args1 <> List.length args2) then (cache, false)
      else List.fold_left2 subtype_sigma_list (cache, true) ((STyp t1)::args1) ((STyp t2)::args2)
    | TArrow (_, args1, None, ret1), TArrow (_, args2, None, ret2) ->
      if (List.length args1 <> List.length args2) then (cache, false)
      else (List.fold_left2 subtype_typ_list (cache, true) (ret1::args1) (ret2::args2))
    | TArrow (_, args1, None, ret1), TArrow (_, args2, Some var2, ret2) ->
      if (List.length args1 < List.length args2) then (cache, false)
      else 
        let args2' = fill (List.length args1 - List.length args2) var2 args2 in
        (List.fold_left2 subtype_typ_list (cache, true) (ret1::args1) (ret2::args2'))
    | TArrow (_, args1, Some var1, ret1), TArrow (_, args2, None, ret2) ->
      if (List.length args1 > List.length args2) then (cache, false)
      else 
        let args1' = fill (List.length args2 - List.length args1) var1 args1 in
        (List.fold_left2 subtype_typ_list (cache, true) (ret1::args1') (ret2::args2))
    | TArrow (_, args1, Some var1, ret1), TArrow (_, args2, Some var2, ret2) ->
      if (List.length args1 > List.length args2) then
        let args2' = fill (List.length args1 - List.length args2) var2 args2 in
        (List.fold_left2 subtype_typ_list (cache, true) (ret1::args1) (ret2::args2'))
      else 
        let args1' = fill (List.length args2 - List.length args1) var1 args1 in
        (List.fold_left2 subtype_typ_list (cache, true) (ret1::args1') (ret2::args2))
    | TForall (_, x1, s1, t1), TForall (_, x2, s2, t2) -> 
      (* Kernel rule *)
      if not (equivalent_sigma env s1 s2) then cache, false
      else 
        let t2 = typ_typ_subst x2 (TId x1) t2 in
        let env' = match s2 with
          | STyp t -> IdMap.add x1 (BTypBound (t, KStar)) env
          | SMult m -> IdMap.add x1 (BMultBound (m, KMult KStar)) env in
        subtype_typ env' cache t1 t2
    | _ -> (cache, false))
  end
    
and subtype_mult lax env cache m1 m2 = 
  let subtype_mult = subtype_mult lax env in
  let subtype_typ = subtype_typ lax env in (* ok for now because there are no MId binding forms in Mult *)
  let open SigmaPair in
  let addToCache (cache, ret) = (SPMap.add (project_mults m1 m2 env, SMults (m1, m2)) ret cache, ret) in
  try (cache, SPMap.find (project_mults m1 m2 env, SMults (m1, m2)) cache)
  with Not_found -> addToCache (match m1, m2 with
  | MId n1, t2 when t2 = MId n1 -> cache, true (* SA-Refl-TVar *)
  | MId n1, _ -> (* SA-Trans-TVar *)
    (try
       (match IdMap.find n1 env with 
       | BMultBound (m1, _) -> subtype_mult cache m1 m2
       | _ -> cache, false)
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
