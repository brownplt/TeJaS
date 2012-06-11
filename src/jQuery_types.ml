open Prelude
open Sig
open ListExt

module Make (Pat : SET) = struct

  let num_typ_errors = ref 0

  let error_on_mismatch = ref false

  let with_typ_exns thunk = 
    let prev = !error_on_mismatch in
    error_on_mismatch := true;
    let r = thunk () in
    error_on_mismatch := prev;
    r

  let get_num_typ_errors () = !num_typ_errors

  type pat = Pat.t
  module Pat = Pat
  module P = Pat


  type kind = 
    | KStar
    | KMult of kind
    | KArrow of kind list * kind

  type typ = 
    | TBot
    | TTop
    | TUnit
    | TPrim of string
    | TRegex of pat
    | TId of id
    | TUnion of string option * typ * typ
    | TInter of string option * typ * typ
    | TForall of string option * id * sigma * typ
    | TArrow of string option * typ list * typ option * typ
    | TLambda of string option * (id * kind) list * typ
    | TApp of typ * sigma list
  and multiplicity = 
    | MPlain of typ
    | MId of id
    | MZero of multiplicity
    | MOne of multiplicity
    | MZeroOne of multiplicity
    | MOnePlus of multiplicity
    | MZeroPlus of multiplicity
    | MSum of multiplicity * multiplicity
  and sigma = STyp of typ | SMult of multiplicity

  type typenv = (typ * kind) IdMap.t

  let rec apply_name n typ = match typ with
    | TUnion(None, t1, t2) -> TUnion(n, t1, t2)
    | TInter(None, t1, t2) -> TInter(n, t1, t2)
    | TForall(None, x, t, b) -> TForall(n, x, t, b)
    | TArrow(None, t1, t2, t3) -> TArrow(n, t1, t2, t3)
    | _ -> typ

  and name_of typ =  match typ with
    | TUnion(name, _, _) -> name
    | TInter(name, _, _) -> name
    | TForall(name, _, _, _) -> name
    | TArrow(name, _, _, _) -> name
    | _ -> None

  and replace_name n typ = match typ with
    | TUnion(_, t1, t2) -> TUnion(n, t1, t2)
    | TInter(_, t1, t2) -> TInter(n, t1, t2)
    | TForall(_, x, t, b) -> TForall(n, x, t, b)
    | TArrow(_, t1, t2, t3) -> TArrow(n, t1, t2, t3)
    | _ -> typ


  (* pretty printing *)
  module Pretty = struct
    open Format
    open FormatExt

    let useNames = ref true
    let rec kind k = match k with
      | KStar -> text "*"
      | KMult k -> squish [text "M"; angles (kind k)]
      | KArrow (ks, k) -> 
        horz [horz (intersperse (text ",") (map pr_kind ks)); text "=>"; kind k]
    and pr_kind k = match k with
      | KArrow _ -> parens (kind k)
      | _ -> kind k


    let rec typ t = typ' false t
    and typ' horzOnly t =
      let typ = typ' horzOnly in
      let hnestOrHorz n = if horzOnly then horz else (fun ps -> hnest n (squish ps)) in
      let namedType name fmt = 
        if !useNames 
        then match name with None -> fmt | Some n -> text n 
        else match name with None -> horz [text "Unnamed"; fmt] | Some n -> horz [text "Named"; text n; fmt] in
      let p = typ in 
      match t with
      | TBot -> text "Bot"
      | TTop -> text "Top"
      | TUnit -> text "()"
      | TPrim s -> text ("@" ^ s)
      | TRegex pat -> text (P.pretty pat)
      | TId name -> squish [text "'"; text name]
      | TUnion (name, t1, t2) -> namedType name (parens (horzOrVert [horz[p t1; text "U"]; p t2]))
      | TInter (name, t1, t2) -> namedType name (parens (horzOrVert [horz[p t1; text "&"]; p t2]))
      | TForall (name, alpha, bound, body) -> begin
        let binding = match bound with
          | STyp TTop -> text alpha
          | STyp t -> horz [text alpha; text "<:"; typ t]
          | SMult m -> horz [text alpha; text "<:"; multiplicity m]
        in
        namedType name (horzOrVert [horz [text "Forall"; binding; text "."];
                                    typ body])
      end
      | TLambda (n, args, t) -> 
        let p (x, k) = horz [ text x; text "::"; kind k ] in
        namedType n (hvert [horz [text "Lambda"; horz (map p args); text "."]; typ t ])
      | TApp (t, ts) ->
        (match ts with
        | [] -> horz [typ t; text "<>"]
        | _ -> parens (squish [typ t; angles (horz (intersperse (text ",") (map sigma ts)))]))
      | TArrow (name, tt::arg_typs, varargs, r_typ) ->
        let multiLine = horzOnly ||
          List.exists (fun at -> match at with 
            TArrow _ -> true | _ -> false) arg_typs in
        let rec pairOff ls = match ls with
          | [] -> []
          | [_] -> ls
          | a::b::ls -> horz [a;b] :: pairOff ls in
        let vararg = match varargs with
          | None -> []
          | Some t -> [horz[squish [parens(horz[typ' true t]); text "..."]]] in
        let argTexts = 
          (intersperse (text "*") 
             ((map (fun at -> begin match at with
             | TArrow _ -> parens (horz [typ' true at])
             | _ -> typ' true at 
             end) arg_typs) @ vararg)) in
        namedType name 
          (hnestOrHorz 0
             [ squish [brackets (typ tt); 
                       (if multiLine 
                        then vert (pairOff (text " " :: argTexts)) 
                        else horz (empty::argTexts))] ;
               horz [text "->"; typ r_typ ]])
      | TArrow (name, arg_typs, varargs, r_typ) ->
        let vararg = match varargs with
          | None -> []
          | Some t -> [horz[squish [parens(horz[typ' true t]); text "..."]]] in
        let argText = horz (intersperse (text "*") 
                              ((map (fun at -> begin match at with
                              | TArrow _ -> parens (horz [typ' true at])
                              | _ -> typ' true at 
                              end) arg_typs) @ vararg)) in
        namedType name (hnestOrHorz 0 [ argText; horz [text "->"; typ r_typ ]])
    and multiplicity m =
      let p = multiplicity in
      match m with
      | MPlain t -> typ t
      | MId name -> squish [text "`"; text name]
      | MZero m -> squish [text "0"; angles (p m)]
      | MOne m -> squish [text "1"; angles (p m)]
      | MZeroOne m -> squish [text "01"; angles (p m)]
      | MOnePlus m -> squish [text "1+"; angles (p m)]
      | MZeroPlus m -> squish [text "0+"; angles (p m)]
      | MSum(m1, m2) -> squish [text "Sum"; angles (horzOrVert [horz[p m1; text "++"]; p m2])]
    and sigma s = match s with
      | STyp t -> typ t
      | SMult m -> multiplicity m
  end

(* free type variables *)
  let rec free_sigma_ids s = match s with
    | STyp t -> free_typ_ids t
    | SMult m -> free_mult_ids m
  and free_mult_ids m : IdSet.t * IdSet.t = 
    let open IdSet in
    let open IdSetExt in
    match m with
    | MPlain t -> free_typ_ids t
    | MId name -> (empty, singleton name)
    | MZero m
    | MOne m
    | MZeroOne m
    | MOnePlus m
    | MZeroPlus m -> free_mult_ids m
    | MSum(m1, m2) ->
      let (f1t, f1m) = (free_mult_ids m1) in
      let (f2t, f2m) = (free_mult_ids m2) in
      (union f1t f2t, union f1m f2m)
  and free_typ_ids t =
    let open IdSet in
    let open IdSetExt in
    match t with
    | TBot
    | TTop
    | TUnit
    | TPrim _
    | TRegex _ -> (empty, empty)
    | TId x -> (singleton x, empty)
    | TLambda (_, xks, t) -> let (ts, ms) = (free_typ_ids t) in (diff ts (from_list (map fst2 xks)), ms)
    | TApp (t, ss) -> map_pair unions (List.split (free_typ_ids t :: (map free_sigma_ids ss)))
    | TInter (_, t1, t2)
    | TUnion (_, t1, t2) ->
      let (f1t, f1m) = (free_typ_ids t1) in
      let (f2t, f2m) = (free_typ_ids t2) in
      (union f1t f2t, union f1m f2m)
    | TArrow (_, args, var, ret) ->
      List.fold_left (fun (t, m) arg ->
        let (argt, argm) = free_typ_ids arg in
        (union t argt, union m argm)) (free_typ_ids ret) (match var with None -> args | Some v -> v::args)
    | TForall (_, alpha, bound, typ) ->
      let (f1t, f1m) = (free_sigma_ids bound) in
      let (f2t, f2m) = (free_typ_ids typ) in
      (remove alpha (union f1t f2t), union f1m f2m)

  let rec subst x (s : sigma) (sigma : sigma) : sigma =
    let rec sigma_help sigma : sigma = match sigma with
      | STyp typ -> STyp (typ_help typ)
      | SMult mult -> SMult (mult_help mult)
    and mult_help mult : multiplicity = match mult with
      | MPlain typ -> MPlain (typ_help typ)
      | MId y -> if x = y then match s with SMult m -> m | STyp _ -> mult else mult
      | MZero m -> MZero (mult_help m)
      | MOne m -> MOne (mult_help m)
      | MZeroOne m -> MZeroOne (mult_help m)
      | MOnePlus m -> MOnePlus (mult_help m)
      | MZeroPlus m -> MZeroPlus (mult_help m)
      | MSum (m1, m2) -> MSum (mult_help m1, mult_help m2)
    and typ_help typ : typ = match typ with
      | TBot
      | TTop
      | TUnit
      | TPrim _ 
      | TRegex _ -> typ
      | TApp(f, args) -> TApp(typ_help f, List.map sigma_help args)
      | TLambda (n, yks, t) ->
        let ys = IdSetExt.from_list (map fst2 yks) in
        if IdSet.mem x ys then
          typ
        else begin
          let fresh_var old = (* a, b, ... z, aa, bb, ..., zz, ... *)
            let rec try_ascii m n =
              let attempt = String.make m (Char.chr n) in
              if not (List.mem attempt old) then attempt
              else if (n < int_of_char 'z') then try_ascii m (n+1)
              else try_ascii (m+1) (Char.code 'a') in
            try_ascii 1 (Char.code 'a') in
          let (free_t, free_m) = free_sigma_ids s in
          let (rev_new_yks, typ_substs, mult_substs) =
            List.fold_left (fun (new_yks, typ_substs, mult_substs) (y, k) ->
              match k with
              | KStar
              | KArrow _ -> 
                if not (IdSet.mem y free_t) then ((y,k)::new_yks, typ_substs, mult_substs)
                else 
                  let x = fresh_var (IdMapExt.keys typ_substs) in
                  ((x,k)::new_yks, IdMap.add y (STyp (TId x)) typ_substs, mult_substs)
              | KMult _ ->
                if not (IdSet.mem y free_m) then ((y,k)::new_yks, typ_substs, mult_substs)
                else 
                  let x = fresh_var (IdMapExt.keys mult_substs) in
                  ((x,k)::new_yks, typ_substs, IdMap.add y (SMult (MId x)) mult_substs))
              ([], IdMap.empty, IdMap.empty) yks in
          let new_yks = List.rev rev_new_yks in
          let t' = IdMap.fold subst typ_substs (STyp t) in
          let t'' = IdMap.fold subst mult_substs t' in
          let t''' = match t'' with STyp t -> t | _ -> failwith "impossible" in
          TLambda (n, new_yks, typ_help t''')
        end
      | TId y -> if x = y then match s with STyp t -> t | SMult _ -> typ else typ
      | TInter (name, t1, t2) -> TInter (name, typ_help t1, typ_help t2)
      | TUnion (name, t1, t2) -> TUnion (name, typ_help t1, typ_help t2)
      | TArrow (name, args, var, ret) -> TArrow (name, map typ_help args, opt_map typ_help var, typ_help ret)
      | TForall (name, alpha, bound, body) -> if x = alpha then typ else
          TForall (name, alpha, sigma_help bound, typ_help body)
    in sigma_help sigma

  let typ_typ_subst x t typ = match subst x (STyp t) (STyp typ) with STyp t -> t | _ -> failwith "impossible"
  let typ_mult_subst x t m = match subst x (STyp t) (SMult m) with SMult m -> m | _ -> failwith "impossible"
  let mult_typ_subst x m t = match subst x (SMult m) (STyp t) with STyp t -> t | _ -> failwith "impossible"
  let mult_mult_subst x m mult = match subst x (SMult m) (SMult mult) with SMult m -> m | _ -> failwith "impossible"

(* simple equivalence *)
  let rec simpl_equiv t1 t2 = if (replace_name None t1) = (replace_name None t2) then true else match t1, t2 with
    | TForall(_, alpha, bound1, typ1), TForall(_, beta, bound2, typ2) ->
      begin match bound1, bound2 with
      | STyp b1, STyp b2 -> simpl_equiv b1 b2 && 
        (if alpha = beta then simpl_equiv typ1 typ2
         else simpl_equiv (typ_typ_subst alpha (TId beta) typ1) typ2)
      | SMult m1, SMult m2 -> (m1 = m2) &&
        (if alpha = beta then simpl_equiv typ1 typ2
         else simpl_equiv (typ_typ_subst alpha (TId beta) typ1) typ2)
      | _, _ -> false
      end
    | _ -> false

(* canonical forms *)
  let rec canonical_sigma s = match s with
    | STyp t -> STyp (canonical_type t)
    | SMult m -> SMult (canonical_multiplicity m)

  and canonical_type t =
    let rec c = canonical_type in
    match t with
    | TBot -> t
    | TTop -> t
    | TUnit -> t
    | TPrim _ -> t
    | TRegex _ -> t
    | TId _ -> t
    | TApp(f, args) -> TApp(c f, List.map canonical_sigma args)
    | TLambda(n, yks, t) -> TLambda(n, yks, c t)
    | TUnion (n, _, _) -> begin
      let rec collect t = match t with
        | TUnion (_, t1, t2) -> collect (c t1) @ collect (c t2)
        | _ -> [t] in
      let pieces = collect t in
      let nodups = remove_dups pieces in
      match List.rev nodups with
      | [] -> failwith "impossible"
      | hd::tl -> apply_name n (List.fold_left (fun acc t -> if t = TBot then acc else TUnion(None, t, acc)) hd tl)
    end
    | TInter (n, TUnion (_, u1, u2), t) -> c (TUnion (n, c (TInter (None, u1, t)), c (TInter (None, u2, t))))
    | TInter (n, t, TUnion (_, u1, u2)) -> c (TUnion (n, c (TInter (None, t, u1)), c (TInter (None, t, u2))))
    | TInter (n, t1, t2) -> begin match c t1, c t2 with
      | TTop, t
      | t, TTop -> t
      | TBot, _
      | _, TBot -> TBot
      | (TForall(_, alpha, bound1, typ1) as t1), (TForall(_, beta, bound2, typ2) as t2) -> begin
        match bound1, bound2 with
        | STyp b1, STyp b2 -> 
          if simpl_equiv b1 b2 
          then TForall(n, alpha, bound1, canonical_type (TInter (None, typ1, typ_typ_subst beta (TId alpha) typ2)))
          else TInter(n, t1, t2)
        | _, _ -> TInter(n, t1, t2)
      end
      | t1, t2 -> if t1 = t2 then t1 else TInter(n, t1, t2)
    end
    | TForall (n, alpha, bound, typ) -> TForall(n, alpha, canonical_sigma bound, c typ)
    | TArrow (n, args, var, ret) -> TArrow (n, map c args, opt_map c var, c ret)

  and canonical_multiplicity m = 
    let c = canonical_multiplicity in
  (* Invariant: will never return MPlain or MId, and
   * if there are no MIds then it will never return MSum *)
    match m with
    | MPlain t -> MOne (MPlain (canonical_type t))
    | MId _ -> MOne m
    | MZero _ -> MZero (MPlain TUnit)
    | MOne m -> c m
    | MZeroOne (MPlain t) -> MZeroOne (MPlain (canonical_type t))
    | MZeroOne (MId _) -> m
    | MZeroOne (MZero m) -> c (MZero m)
    | MZeroOne (MOne m) -> c (MZeroOne m)
    | MZeroOne (MZeroOne m) -> c (MZeroOne m)
    | MZeroOne (MOnePlus m) -> c (MZeroPlus m)
    | MZeroOne (MZeroPlus m) -> c (MZeroPlus m)
    | MZeroOne (MSum (m1, m2)) -> let m' = MZeroOne (c (MSum (m1, m2))) in if m' = m then m else c m'
    | MOnePlus (MPlain t) -> MOnePlus (MPlain (canonical_type t))
    | MOnePlus (MId _) -> m
    | MOnePlus (MZero m) -> c (MZero m)
    | MOnePlus (MOne m) -> c (MOnePlus m)
    | MOnePlus (MZeroOne m) -> c (MZeroPlus m)
    | MOnePlus (MOnePlus m) -> c (MOnePlus m)
    | MOnePlus (MZeroPlus m) -> c (MZeroPlus m)
    | MOnePlus (MSum (m1, m2)) -> let m' = MOnePlus (c (MSum (m1, m2))) in if m' = m then m else c m'
    | MZeroPlus (MPlain t) -> MZeroPlus (MPlain (canonical_type t))
    | MZeroPlus (MId _) -> m
    | MZeroPlus (MZero m) -> c (MZero m)
    | MZeroPlus (MOne m) -> c (MZeroPlus m)
    | MZeroPlus (MZeroOne m) -> c (MZeroPlus m)
    | MZeroPlus (MOnePlus m) -> c (MZeroPlus m)
    | MZeroPlus (MZeroPlus m) -> c (MZeroPlus m)
    | MZeroPlus (MSum (m1, m2)) -> let m' = MZeroPlus (c (MSum (m1, m2))) in if m' = m then m else c m'
    | MSum(m1, m2) -> match c m1, c m2 with
      | MZero _, t2 -> t2
      | t1, MZero _ -> t1
      | MOne (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MOne (MPlain t1), MZeroOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MOne (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MOne (MPlain t1), MZeroPlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroOne (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroOne (MPlain t1), MZeroOne (MPlain t2) -> MZeroPlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroOne (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroOne (MPlain t1), MZeroPlus (MPlain t2) -> MZeroPlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MOnePlus (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MOnePlus (MPlain t1), MZeroOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MOnePlus (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MOnePlus (MPlain t1), MZeroPlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroPlus (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroPlus (MPlain t1), MZeroOne (MPlain t2) -> MZeroPlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroPlus (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MZeroPlus (MPlain t1), MZeroPlus (MPlain t2) -> MZeroPlus (MPlain (canonical_type (TUnion(None, t1, t2))))
      | MPlain _, _
      | MId _, _
      | _, MPlain _
      | _, MId _ -> failwith "impossible"
      | t1, t2 -> MSum (t1, t2)


  (* subtyping *)
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
    let subtype_typ = subtype_typ lax env in
    let open SigmaPair in
    let (|||) c thunk = if (snd c) then c else thunk (fst c) in
    let (&&&) c thunk = if (snd c) then thunk (fst c) else c in
    let subtype_typ_list c t1 t2 = c &&& (fun c -> subtype_typ c t1 t2) in
    let subtype_sigma_list c t1 t2 = c &&& (fun c -> subtype_sigma lax env c t1 t2) in
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
      | TId n1, TId n2 -> (cache, n1 = n2)
      | t1, TUnion(_, t21, t22) ->
        subtype_typ cache t1 t21 ||| (fun c -> subtype_typ c t1 t22)
      | t1, TInter(_, t21, t22) ->
        subtype_typ cache t1 t21 &&& (fun c -> subtype_typ c t1 t22)
      | TUnion(_, t11, t12), t2 ->
        subtype_typ cache t11 t2 &&& (fun c -> subtype_typ c t12 t2)
      | TInter(_, t11, t12), t2 ->
        subtype_typ cache t11 t2 ||| (fun c -> subtype_typ c t12 t2)
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
      (* still need to handle TForall... *)
      | _ -> (cache, false))
    end
      
  and subtype_mult lax env cache m1 m2 = 
    let subtype_mult = subtype_mult lax env in
    let subtype_typ = subtype_typ lax env in
    let open SigmaPair in
    let addIfSuccess (cache, ret) = (SPMap.add (SMults (m1, m2)) ret cache, ret) in
    try (cache, SPMap.find (SMults (m1, m2)) cache)
    with Not_found -> addIfSuccess (match m1, m2 with
    | MId x, MId y -> (cache, x = y) (* not canonical, but easy enough *)
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

(* SUBTYPING ONLY WORKS ON CANONICAL FORMS *)
  let subtype_sigma lax env s1 s2 =
    snd (subtype_sigma lax env SPMap.empty (canonical_sigma s1) (canonical_sigma s2))
  let subtype_typ lax env t1 t2 =
    snd (subtype_typ lax env SPMap.empty (canonical_type t1) (canonical_type t2))
  let subtype_mult lax env m1 m2 =
    snd (subtype_mult lax env SPMap.empty (canonical_multiplicity m1) (canonical_multiplicity m2))


  exception Typ_error of Pos.t * string
  let typ_mismatch p s = 
    if !error_on_mismatch then
      raise (Typ_error (p, s))
    else begin
      incr num_typ_errors;
      eprintf "type error at %s : %s\n" (Pos.toString p) s
    end

  let string_of_typ = FormatExt.to_string Pretty.typ
  let string_of_kind = FormatExt.to_string Pretty.kind

  (* UNIFICATION *)
  let (&&&) opt thunk = match opt with None -> None | Some c -> thunk c
  type sconstraint = Bound of sigma | Equal of sigma
  type constraintTable = sconstraint list IdMap.t
  let addConstraint id constr table =
    try 
      let existing = IdMap.find id table in
      IdMap.add id (constr::existing) table
    with Not_found ->
      IdMap.add id [constr] table
  let rec collect_unify_sigma c s1 s2 : (constraintTable * constraintTable) option =
    match s1, s2 with
    | STyp t1, STyp t2 -> collect_unify_typ c t1 t2
    | SMult m1, SMult m2 -> collect_unify_mult c m1 m2
    | _, _ -> Some (IdMap.empty, IdMap.empty)
  and collect_unify_typ (typs, mults) t1 t2 = 
    match t1, t2 with
    | TBot, TBot
    | TTop, TTop
    | TUnit, TUnit -> Some (typs, mults)
    | TUnion(_, t11, t12), TUnion(_, t21, t22)
    | TInter(_, t11, t12), TInter(_, t21, t22) ->
      collect_unify_typ (typs, mults) t11 t21 &&&
        (fun c -> collect_unify_typ c t12 t22)
    | TArrow(_, args1, var1, ret1), TArrow(_, args2, var2, ret2) ->
      if (List.length args1 <> List.length args2) then None
      else 
        let args1' = match var1 with None -> args1 | Some v -> v :: args1 in
        let args2' = match var2 with None -> args2 | Some v -> v :: args2 in
        List.fold_left2 (fun c t1 t2 -> c &&& (fun c -> collect_unify_typ c t1 t2)) 
          (Some (typs, mults)) (ret1::args1') (ret2::args2')
    | TId x, t
    | t, TId x -> begin
      if (t == TId x) then (Some (typs, mults))
      else if (IdSet.mem x (fst (free_typ_ids t))) then None (* occurs check failed *)
      else (* ought to check kinds *)
        Some (addConstraint x (Equal (STyp t)) typs, mults)
    end
    | TForall(_, alpha, bound, body), t
    | t, TForall(_, alpha, bound, body) ->
      begin match bound with
      | STyp _ ->
        let typs' = addConstraint alpha (Bound bound) typs in
        collect_unify_typ (typs', mults) t body
      | SMult _ ->
        let mults' = addConstraint alpha (Bound bound) mults in
        collect_unify_typ (typs, mults') t body
      end
    | _ -> None
  and collect_unify_mult (typs, mults) m1 m2 = 
    match m1, m2 with
    | MPlain t1, MPlain t2 -> collect_unify_typ (typs, mults) t1 t2
    | MZero m1, MZero m2
    | MOne m1, MOne m2
    | MZeroOne m1, MZeroOne m2
    | MOnePlus m1, MOnePlus m2
    | MZeroPlus m1, MZeroPlus m2 ->
      collect_unify_mult (typs, mults) m1 m2
    | MSum(m11, m12), MSum(m21, m22) ->
      collect_unify_mult (typs, mults) m11 m21 &&&
        (fun c -> collect_unify_mult c m12 m22)
    | MId x, m
    | m, MId x -> Some (typs, addConstraint x (Equal (SMult m)) mults)
    | _ -> None
end

