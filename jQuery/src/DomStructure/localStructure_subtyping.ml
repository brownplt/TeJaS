open LocalStructure_syntax
open JQuery_env
open Css
open Css_syntax
open JQuery_syntax
open TypImpl


  
let rec expose_TDom (env : env) (t : typ) : typ = match t with
  | TDom (s, (TDom (_,t,sel2)), sel1) ->
    expose_TDom env (TDom (s, t, Css.intersect sel2 sel1))
  | TDom (s, (TId id), sel) -> 
    expose_TDom env (TDom (s, fst (lookup_typ_id id env), sel))
  | _ -> t

let backform (benv : backformEnv) (sels : sel) : LSIdSet.t =
  let rec list2lsidset l = (match l with
    | [] -> LSIdSet.empty
    | h::t -> LSIdSet.add h (list2lsidset t)) in
  let simples = Css.targets sels in
  let classes = SimpleSelSet.fold (fun (a,specs) (acc : string list)->
    (acc @ (List.fold_left (fun acc s -> match s with 
    | SpClass s -> s::acc
    | _ -> acc) [] specs))) simples [] in
  let (BackformEnv (classMap, _, _)) = benv in
  let classMatches = match classes with
    | [] -> LSIdSet.empty
    | hd::tl -> List.fold_left (fun acc c ->
      try LSIdSet.inter acc (list2lsidset (StringMap.find c classMap))
      with Not_found -> LSIdSet.empty)
      (try (list2lsidset (StringMap.find
                            hd
                            classMap))
       with Not_found -> LSIdSet.empty)
      tl in
  classMatches

let children_of (senv : structureEnv) (t : typ) : multiplicity = 
  let ClauseEnv (childMap, _, _, _) = (snd senv) in 
  let get_children_of t = 
    match t with
    | TDom (s,t,sels) ->
      let lsidSet = backform (fst senv) sels in
      (LSIdSet.fold (fun lsid acc ->
        (try MSum (acc, LSIdMap.find lsid childMap)
         with Not_found -> failwith "impossible") (* Backform has ALL lsids *))
         lsidSet 
         (MZero (MPlain (TDom (None, TId "ElementAny", Css.singleton "*")))))
    | TId id -> LSIdMap.find (LSId id) childMap (* TODO: is this ok? *) 
    | _ -> failwith "impossible: childrenOf called on a multiplicity containing somethign other than a TDom or TId" in
  (* build children and canonicalize result *)
  get_children_of t
    
  (* TODO: make recursive, descend *)
let rec resolve_special_functions (env : env) (senv : structureEnv) (t : typ) = 
  let rsf = resolve_special_functions env senv in
  let rec resolve_mult m = 
    let rm = resolve_mult in 
    match m with
    | MPlain t -> MPlain (rsf t)
    | MId _ -> m
    | MZero m-> MZero (rm m)
    | MOne m -> MOne (rm m)
    | MZeroOne m -> MZeroOne (rm m)
    | MOnePlus m -> MOnePlus (rm m)
    | MZeroPlus m -> MZeroPlus (rm m)
    | MSum (m1, m2) -> MSum (rm m1, rm m2) in
  let resolve_sigma s = match s with
    | STyp t -> STyp (rsf t)
    | SMult m -> SMult (resolve_mult m) in
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
    | MSum _ -> failwith "can't handle MSums here" in
  match t with
  | TPrim s -> t
  | TId id -> t
  | TUnion (s,t1,t2) -> TUnion(s, rsf t1, rsf t2)
  | TInter (s,t1,t2) -> TInter(s, rsf t1, rsf t2)
  | TForall (s,id,sigma,t) -> TForall(s,id,sigma, rsf t)
  | TArrow (s,ts,t1,t2) -> 
    TArrow(s, 
           List.map rsf ts, 
           (match t1 with None -> None | Some t -> Some (rsf t)),
           rsf t2)
  | TLambda (s,iks,t) -> TLambda(s,iks,rsf t)
  | TApp(TPrim "childrenOf", [STyp t]) -> 
    failwith "childrenOf at outermost level"
  | TApp(t, args) ->
    TApp(rsf t, List.map (fun s -> match s with
    | SMult m -> begin match extract_mult m with
      | TApp(TPrim "childrenOf", [STyp t]), m ->
        SMult (canonical_multiplicity (m (children_of senv (rsf t))))
      | TApp(TPrim "childrenOf", _), _ ->
        failwith "childrenOf not called with a single type argument"
      | _, _ -> SMult m
    end
    | STyp _ -> s) args)
  | TRec (s,id,t) -> TRec (s, id, rsf t)
  | TDom (s, t, sel) -> TDom (s, rsf t, sel)
  | _ -> t

    


