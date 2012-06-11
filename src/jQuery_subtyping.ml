open Prelude
open JQuery_syntax
open TypImpl
open ListExt

module SigmaPair = struct
  type t = STyps of typ * typ | SMults of multiplicity * multiplicity | SMultTyp of multiplicity * typ
  let compare = Pervasives.compare
end
module SPMap = Map.Make (SigmaPair)
module SPMapExt = MapExt.Make (SigmaPair) (SPMap)


let rec subtype_sigma lax env cache s1 s2 = 
  let open SigmaPair in
  match s1, s2 with
  | STyp t1, STyp t2 -> subtype_typ lax env cache t1 t2
  | SMult m1, SMult m2 -> subtype_mult lax env cache m1 m2
  (* SUPER-CRITICAL LAXITY RULE *)
  | SMult m1, STyp t2 -> 
    if lax then
      let (cache, ret) = subtype_mult lax env cache m1 (MZeroPlus (MPlain t2)) in
      (SPMap.add (SMultTyp (m1, t2)) ret cache, ret)
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
  let addIfSuccess (cache, ret) = (SPMap.add (STyps (t1, t2)) ret cache, ret) in
  try (cache, SPMap.find (STyps (t1, t2)) cache)
  with Not_found -> begin addIfSuccess (if simpl_equiv t1 t2 
    then (cache, true)
    else match t1, t2 with
    | _, TTop
    | TBot, _ -> (cache, true)
    | TRegex pat1, TRegex pat2 ->
      (cache, P.is_subset IdMap.empty pat1 pat2)
    | TPrim p1, TPrim p2 -> (cache, p1 = p2)
    | TId n1, TId n2 -> (cache, n1 = n2) ||| (fun c ->
      try
        let (t1, _) = IdMap.find n1 (fst env) in
        let (t2, _) = IdMap.find n2 (fst env) in
        subtype_typ env c t1 t2
      with Not_found -> (c, false))
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
      subtype_sigma env cache s1 s2 (* bounds must be invariant, since e.g. *)
      &&& (fun c -> subtype_sigma env c s2 s1) (* (forall a <: int. ref a) !<: (forall a <: Top. ref a) *)
      &&& (fun c ->
        let t2 = typ_typ_subst x2 (TId x1) t2 in
        let env' = match s1 with
          | STyp t -> (IdMap.add x1 (t, KStar) (fst env), snd env)
          | SMult m -> (fst env, IdMap.add x1 (m, KMult KStar) (snd env)) in
        subtype_typ env' c t1 t2)
    | _ -> (cache, false))
  end
    
and subtype_mult lax env cache m1 m2 = 
  let subtype_mult = subtype_mult lax env in
  let subtype_typ = subtype_typ lax env in (* ok for now because there are no MId binding forms in Mult *)
  let open SigmaPair in
  let (|||) c thunk = if (snd c) then c else thunk (fst c) in
  let addIfSuccess (cache, ret) = (SPMap.add (SMults (m1, m2)) ret cache, ret) in
  try (cache, SPMap.find (SMults (m1, m2)) cache)
  with Not_found -> addIfSuccess (match m1, m2 with
  | MId x, MId y -> (cache, x = y) ||| (fun c ->
    try
      let (mx, _) = IdMap.find x (snd env) in
      let (my, _) = IdMap.find y (snd env) in
      subtype_mult c mx my
    with Not_found -> (c, false))
  | MPlain t1, MPlain t2 -> subtype_typ cache t1 t2 (* ditto *)
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
  | MPlain _, _
  | MId _, _ -> (cache, false) (* not canonical! *)
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
