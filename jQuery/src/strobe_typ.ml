open Prelude
open Sig
open Strobe_sigs

module L = ListExt

module Make : STROBE_TYP = functor (Pat : SET) -> functor (EXT : TYPS) -> struct

  type pat = Pat.t

  type extKind = EXT.kind
  type kind = 
    | KStar
    | KArrow of kind list * kind
    | KEmbed of EXT.kind
  
  type presence = 
    | Inherited
    | Present
    | Maybe
  
  type extTyp = EXT.typ
  type typ = 
    | TPrim of string
    | TUnion of string option * typ * typ
    | TInter of string option * typ * typ
    | TArrow of typ list * typ option * typ (* args (including <this>), optional variadic arg, return typ *)
    | TThis of typ
    | TObject of obj_typ
    | TWith of typ * obj_typ
    | TRegex of pat
    | TRef of string option * typ
    | TSource of string option * typ
    | TSink of string option * typ
    | TTop
    | TBot
    | TForall of string option * id * typ * typ (** [TForall (a, s, t)] forall a <: s . t *)
    | TId of id
    | TRec of string option * id * typ 
    | TLambda of string option * (id * kind) list * typ (** type operator *)
    | TApp of typ * typ list (** type operator application *)
    | TFix of string option * id * kind * typ (** recursive type operators *)
    | TUninit of typ option ref (** type of not-yet initialized variables -- write once to the ref to update *)
    | TEmbed of EXT.typ

  and obj_typ = { 
    fields : (pat * presence * typ) list;
    absent_pat : pat;
    cached_parent_typ : typ option option ref;
    cached_guard_pat : pat option ref;
    cached_cover_pat : pat option ref;
    cached_possible_cover_pat : pat option ref; (* pat Lazy.t *)
  }

  type field = pat * presence * typ

  type extBinding = EXT.binding
  type binding = BEmbed of extBinding | BTermTyp of typ | BTypBound of typ * kind

  type env = extBinding IdMap.t
  let proto_str = "__proto__"
    
  let proto_pat = Pat.singleton proto_str

  let fields o = o.fields

  let absent_pat ot = ot.absent_pat

  let possible_field_cover_pat ot = match !(ot.cached_possible_cover_pat) with
    | Some p -> p
    | None -> let ret = Pat.unions (L.map fst3 ot.fields) in
              ot.cached_possible_cover_pat := Some ret;
              ret
  (* Lazy.force ot.cached_possible_cover_pat *)

  let cover_pat ot =  match !(ot.cached_cover_pat) with
    | None -> 
      let p = Pat.union (absent_pat ot) (possible_field_cover_pat ot) in
      ot.cached_cover_pat := Some p;
      p
    | Some p -> p
end

module MakeActions 
  (Pat : SET)
  (STROBE : STROBE_TYPS with type pat = Pat.t)
  (Ext : EXT_TYP_ACTIONS with type typ = STROBE.extTyp with type kind = STROBE.extKind with type binding = STROBE.extBinding with type baseTyp = STROBE.typ with type baseKind = STROBE.kind with type baseBinding = STROBE.binding with type env = STROBE.env)
  : (STROBE_ACTIONS
     with type typ = STROBE.typ with type kind = STROBE.kind with type binding = STROBE.binding with type extTyp = STROBE.extTyp with type extKind = STROBE.extKind with type extBinding = STROBE.extBinding with type pat = STROBE.pat with type obj_typ = STROBE.obj_typ with type env = STROBE.env) =
struct
  include STROBE
  open STROBE



  let apply_name n typ = match typ with
    | TUnion(None, t1, t2) -> TUnion(n, t1, t2)
    | TInter(None, t1, t2) -> TInter(n, t1, t2)
    | TForall(None, x, t, b) -> TForall(n, x, t, b)
    | TRec(None, x, t) -> TRec(n, x, t)
    | TLambda(None, ts, t) -> TLambda(n, ts, t)
    | TFix(None, x, k, t) -> TFix(n, x, k, t)
    | TRef(None, t) -> TRef(n, t)
    | TSource(None, t) -> TSource(n, t)
    | TSink(None, t) -> TSink(n, t)
    | _ -> typ

  let name_of typ =  match typ with
    | TUnion(name, _, _) -> name
    | TInter(name, _, _) -> name
    | TForall(name, _, _, _) -> name
    | TRec(name, _, _) -> name
    | TLambda(name, _, _) -> name
    | TFix(name, _, _, _) -> name
    | TRef(name, _) -> name
    | TSource(name, _) -> name
    | TSink(name, _) -> name
    | _ -> None

  let replace_name n typ = match typ with
    | TUnion(_, t1, t2) -> TUnion(n, t1, t2)
    | TInter(_, t1, t2) -> TInter(n, t1, t2)
    | TForall(_, x, t, b) -> TForall(n, x, t, b)
    | TRec(_, x, t) -> TRec(n, x, t)
    | TLambda(_, ts, t) -> TLambda(n, ts, t)
    | TFix(_, x, k, t) -> TFix(n, x, k, t)
    | TRef(_, t) -> TRef(n, t)
    | TSource(_, t) -> TSource(n, t)
    | TSink(_, t) -> TSink(n, t)
    | _ -> typ


  module Pretty = struct

    open Format
    open FormatExt
      

    let useNames, shouldUseNames =
      let _useNames = ref true in
      let useNames b = _useNames := b in
      let shouldUseNames () = !_useNames in
      useNames, shouldUseNames

    let rec kind k = match k with
      | KEmbed k -> Ext.Pretty.kind k
      | KStar -> text "*"
      | KArrow (ks, k) -> horz [horz (intersperse (text ",") (map pr_kind ks)); text "=>"; kind k]

    and pr_kind k = match k with
      | KArrow _ -> parens [kind k]
      | _ -> kind k
        
    let hnest n (p : printer) (fmt : formatter) : unit =
      pp_open_hvbox fmt n;
      p fmt;
      pp_close_box fmt ()

    let print_space fmt = pp_print_space fmt ()

    let hvert (p : printer list) (fmt : formatter) : unit =
      hnest 2 (squish (intersperse print_space p)) fmt

    let rec typ t = typ' false t
    and typ' horzOnly t = 
      let typ = typ' horzOnly in 
      let hnestOrHorz n = if horzOnly then horz else (fun ps -> hnest n (squish ps)) in
      let namedType name fmt = 
        if shouldUseNames ()
        then match name with None -> fmt | Some n -> text n 
        else match name with None -> horz [text "Unnamed"; fmt] | Some n -> horz [text "Named"; text n; fmt] in
      let namedRef name mut fmt = 
        if shouldUseNames ()
        then match name with None -> fmt | Some n -> squish [text mut; text n] 
        else match name with None -> horz [text "Unnamed*"; fmt] | Some n -> horz [text "Named*"; text n; fmt] in
      match t with
      | TEmbed t -> Ext.Pretty.typ t
      | TTop -> text "Any"
      | TBot -> text "DoesNotReturn"
      | TPrim p -> text ("@" ^ p)
      | TLambda (n, args, t) -> 
        let p (x, k) = horz [ text x; text "::"; kind k ] in
        namedType n (hvert [horz [text "Lambda"; horz (map p args); text "."]; typ t ])
      | TFix (n, x, k, t) -> 
        namedType n (hvert [horz [text "Fix"; text x; text "::"; kind k; text "."]; typ t ])
      | TApp (t, ts) ->
        (match ts with
        | [] -> horz [typ t; text "<>"]
        | _ -> parens [horz [typ t; angles [horz (intersperse (text ",") (map typ ts))]]])
      | TRegex pat -> text (Pat.pretty pat)
      | TUnion (n, t1, t2) ->
        namedType n (
        let rec collectUnions t = match t with
          | TUnion (_, t1, t2) -> 
            let (t1h, t1s) = collectUnions t1 in
            let (t2h, t2s) = collectUnions t2 in
            (t1h, t1s @ (t2h :: t2s))
          | _ -> (t, []) in
        let unions = collectUnions t in
        begin match unions with
        | (t1, [t2]) -> parens [hnestOrHorz 0 [squish [horz [typ t1; text "+"]]; 
                                            if horzOnly then typ t2 else horz[empty;typ t2]]]
        | (t, ts) -> 
          if (List.length ts > 1200) then parens [horz[typ t;
                                                       squish[text "+ ...(";
                                                              int (List.length ts);
                                                              text " total fields)....."]]] else
            parens [hnest (-1) 
                      (squish (intersperse print_space 
                                 ((horz [empty; typ t]) :: List.map (fun t -> horz [text "+"; typ t]) ts)))]
        end)
      | TInter (n, t1, t2) -> (* horz [typ t1; text "&"; typ t2] *)
        namedType n (
        let rec collectIntersections t = match t with
          | TInter (_, t1, t2) -> 
            let (t1h, t1s) = collectIntersections t1 in
            let (t2h, t2s) = collectIntersections t2 in
            (t1h, t1s @ (t2h :: t2s))
          | _ -> (t, []) in
        let intersections = collectIntersections t in
        begin match intersections with
        | (t1, [t2]) -> parens [hnest 0 (squish [squish [horz [typ t1; text "&"]]; 
                                                 if horzOnly then typ t2 else horz[empty;typ t2]])]
        | (t, ts) -> 
          if (List.length ts > 1200) then parens [horz[typ t;
                                                       squish[text "& ...(";
                                                              int (List.length ts);
                                                              text " total fields)....."]]] else
            parens [hnest (-1) 
                      (squish (intersperse print_space 
                                 ((horz [empty; typ t]) :: List.map (fun t -> horz [text "&"; typ t]) ts)))]
        end)
      | TThis t -> squish [text "this"; parens [typ t]]
      | TArrow (tt::arg_typs, varargs, r_typ) ->
        let multiLine = horzOnly ||
          List.exists (fun at -> match at with 
            TArrow _ | TObject _ -> true | _ -> false) arg_typs in
        let rec pairOff ls = match ls with
          | [] -> []
          | [_] -> ls
          | a::b::ls -> horz [a;b] :: pairOff ls in
        let vararg = match varargs with
          | None -> []
          | Some t -> [horz[squish [parens[horz[typ' true t]]; text "..."]]] in
        let argTexts = 
          (intersperse (text "*") 
             ((map (fun at -> begin match at with
             | TArrow _ -> parens [horz [typ' true at]]
             | _ -> typ' true at 
             end) arg_typs) @ vararg)) in
        hnestOrHorz 0
          [ squish [brackets [typ tt];
                    (if multiLine 
                     then vert (pairOff (text " " :: argTexts))
                     else horz (empty::argTexts))] ;
            horz [text "->"; typ r_typ ]]
      | TArrow (arg_typs, varargs, r_typ) ->
        let vararg = match varargs with
          | None -> []
          | Some t -> [horz[squish [parens[horz[typ' true t]]; text "..."]]] in
        let argText = horz (intersperse (text "*") 
                              ((map (fun at -> begin match at with
                              | TArrow _ -> parens [horz [typ' true at]]
                              | _ -> typ' true at 
                              end) arg_typs) @ vararg)) in
        hnestOrHorz 0 [ argText; horz [text "->"; typ r_typ ]]
      | TObject flds -> 
        let isFunctionObject fieldList = 
          let findField namePat =
            try
              let (_, _, typ) =
                List.find (fun (n, p, _) -> (p = Present && n = namePat)) fieldList in
              (true, Some typ)
            with Not_found -> (false, None) in
          let (hasProto, _) = findField proto_pat in
          let (hasCode, codeTyp) = findField (Pat.singleton "-*- code -*-") in
          let (hasPrototype, protoTyp) = findField (Pat.singleton "prototype") in
          let isSimplePrototype = match protoTyp with
            | Some (TId t) -> t = "Object" || t = "Any" || t = "Ext"
                                                || (String.length t > 3 && String.sub t 0 3 = "nsI")
            | _ -> false in
          if ((List.length fieldList) = 4 && hasProto && hasCode && hasPrototype && isSimplePrototype)
          then codeTyp
          else None in
        (match isFunctionObject (flds.fields) with
        | Some arrTyp -> horz [squish [text "{|"; typ' true arrTyp; text "|}"]]
        | None ->
          if (List.length flds.fields > 1200) then braces [squish[text "...(";
                                                                  int (List.length flds.fields);
                                                                  text " total fields)....."]] else
          let abs = horz [ text (Pat.pretty flds.absent_pat); text ": _" ] in
          braces [hnestOrHorz 0 (intersperse print_space (map pat (flds.fields) @ [abs]))]
        )
      | TWith (t, flds) ->
        let abs = horz [ text (Pat.pretty flds.absent_pat); text ": _" ] in
        braces [hnestOrHorz 0 (typ t :: text " with" :: print_space :: 
                                 intersperse print_space (map pat (flds.fields) @ [abs]))]
      | TRef (n, s) -> namedRef n "rw:" (horz [ text "Ref"; parens [typ s] ])
      | TSource (n, s) -> namedRef n "r:" (horz [ text "Src"; parens [typ s] ])
      | TSink (n, s) -> namedRef n "w:" (horz [ text "Snk"; parens [typ s] ])
      | TForall (n, x, s, t) -> 
        namedType n (hvert [ horz [text "forall"; text x; text "<:"; typ s; text "."]; typ t ])
      | TId x -> text x
      | TRec (n, x, t) -> namedType n (horz [ text "rec"; text x; text "."; typ t ])
      | TUninit t -> match !t with
        | None -> text "???"
        | Some t -> squish[text "?"; typ t; text "?"]
  
    and pat (k, pres, p) = 
          let pretty_pres = match pres with
            | Present -> text "!"
            | Maybe -> text "?"
            | Inherited -> text "^" in
          horz [ text (Pat.pretty k); squish [text ":"; pretty_pres]; typ p; text "," ]

    let env env =
      let partition_env e = IdMap.fold (fun i b (ids, typs, others) -> match Ext.extract_b b with
        | BTermTyp t -> (IdMap.add i t ids, typs, others)
        | BTypBound(t, k) -> (ids, IdMap.add i (t, k) typs, others)
        | BEmbed b' -> (ids, typs, IdMap.add i b others)) e (IdMap.empty, IdMap.empty, IdMap.empty) in
      let (id_typs, typ_ids, other) = partition_env env in
      let unname t = if shouldUseNames() then t else replace_name None t in
      let other_print = Ext.Pretty.env other in
      let ids = IdMapExt.p_map "Types of term identifiers: " empty
        text (fun t -> typ (unname t)) 
        id_typs in
      let typs = IdMapExt.p_map "Bounded type variables: " empty
        text 
        (fun (t, k) -> 
          horzOrVert [typ (unname t);
                      horz [text "::"; kind k]]) typ_ids in
      add_sep_between (text ",") ([ids; typs] @ other_print)
  end

  let string_of_typ = FormatExt.to_string Pretty.typ
  let string_of_kind = FormatExt.to_string Pretty.kind


  let rec map_reduce_t (map : extTyp -> 'a) (red : 'b -> 'a -> 'b) b t = match t with
    | TPrim _
    | TTop
    | TBot
    | TId _ -> b
    | TForall(_, _, t1, t2)
    | TUnion (_, t1, t2)
    | TInter (_, t1, t2) -> 
      let b' = map_reduce_t map red b t1 in
      map_reduce_t map red b' t2
    | TArrow(args, var, ret) ->
      let typs = match var with None -> ret::args | Some t -> ret::t::args in
      List.fold_left (map_reduce_t map red) b typs
    | TObject obj -> 
      List.fold_left (map_reduce_t map red) b (List.map thd3 obj.fields)
    (* | TWith _ *)
    | TThis t
    | TRef (_, t)
    | TSource(_, t)
    | TSink(_, t)
    | TRec(_, _, t)
    | TLambda(_, _, t)
    | TFix(_, _, _, t) -> map_reduce_t map red b t
    | TApp(t, ts) ->
      List.fold_left (map_reduce_t map red) (map_reduce_t map red b t) ts
    | TEmbed t -> red b (map t)
    | _ -> b



  let mk_obj_typ (fs: STROBE.field list) (absent_pat : pat): obj_typ = 
    { fields = fs;
      absent_pat = absent_pat;
      cached_parent_typ = ref None;
      cached_guard_pat = ref None;
      cached_possible_cover_pat = ref None; (* lazy (Pat.unions (L.map fst3 fs)); *)
      cached_cover_pat = ref None
    }
  



  let rec free_typ_ids (typ : typ) : IdSet.t =
    let open IdSet in
    let open IdSetExt in
    match typ with
    | TEmbed t -> Ext.free_ids t
    | TTop
    | TBot
    | TPrim _ 
    | TRegex _ -> empty
    | TId x -> singleton x
    | TRef (_, t)
    | TSource (_, t)
    | TSink (_, t) -> free_typ_ids t
    | TInter (_, t1, t2)
    | TUnion (_, t1, t2) -> union (free_typ_ids t1) (free_typ_ids t2)
    | TArrow (ss, v, t) ->
      unions (free_typ_ids t :: (match v with None -> empty | Some v -> free_typ_ids v) :: (map free_typ_ids ss))
    | TThis t -> free_typ_ids t
    | TApp (t, ss) -> unions (free_typ_ids t :: (map free_typ_ids ss))
    | TObject o -> unions (L.map (fun (_, _, t) -> free_typ_ids t) o.fields)
    | TWith(t, flds) -> union (free_typ_ids t) (free_typ_ids (TObject flds))
    | TFix (_, x, _, t)
    | TRec (_, x, t) -> remove x (free_typ_ids t)
    | TForall (_, x, s, t) -> union (free_typ_ids s) (remove x (free_typ_ids t))
    | TLambda (_, xks, t) -> diff (free_typ_ids t) (from_list (map fst2 xks))
    | TUninit t -> match !t with 
      | None -> empty
      | Some ty -> free_typ_ids ty

  let free_ids t = free_typ_ids t

  let rec typ_subst x s outer typ = match typ with
    | TEmbed t -> TEmbed (outer t)
    | TPrim _ -> typ
    | TRegex _ -> typ
    | TId y -> if x = Some y then s else typ
    | TUnion (n, t1, t2) -> TUnion (n, typ_subst x s outer t1, typ_subst x s outer t2)
    | TInter (n, t1, t2) ->
      TInter (n, typ_subst x s outer t1, typ_subst x s outer t2)
    | TArrow (t2s, v, t3)  ->
      let opt_map f v = match v with None -> None | Some v -> Some (f v) in
      TArrow (map (typ_subst x s outer) t2s, opt_map (typ_subst x s outer) v, typ_subst x s outer t3)
    | TThis t -> TThis (typ_subst x s outer t)
    | TWith(t, flds) -> TWith(typ_subst x s outer t, 
                              mk_obj_typ (map (fun (n, p, t) -> (n, p, typ_subst x s outer t)) flds.fields)
                                flds.absent_pat)
    | TObject o ->
        TObject (mk_obj_typ (map (third3 (typ_subst x s outer)) o.fields) 
                            o.absent_pat)
    | TRef (n, t) -> TRef (n, typ_subst x s outer t)
    | TSource (n, t) -> TSource (n, typ_subst x s outer t)
    | TSink (n, t) -> TSink (n, typ_subst x s outer t)
    | TTop -> TTop
    | TBot -> TBot
    | TLambda (n, yks, t) ->
      if List.exists (fun (y, _) -> Some y = x) yks then typ
      else
        let (ys, ks) = List.split yks in
        let free = free_ids s in
        let (new_ys, t') = rename_avoid_capture free ys t in
        let new_yks = List.combine new_ys ks in
        TLambda (n, new_yks, typ_subst x s outer t')
    | TFix (n, y, k, t) ->
      if x = Some y then typ
      else begin
        let free = free_ids s in
        let (newys, t') = rename_avoid_capture free [y] t in
        TFix (n, List.hd newys, k, typ_subst x s outer t')
      end
    | TForall (n, y, t1, t2) -> 
      if x = Some y then typ
      else 
        let free = free_ids s in
        let (beta, t2') = rename_avoid_capture free [y] t2 in
        TForall (n, (List.hd beta), typ_subst x s outer t1, typ_subst x s outer t2')
    | TRec (n, y, t) ->
      if x = Some y then typ
      else begin
        let free = free_ids s in
        let (beta, t') = rename_avoid_capture free [y] t in
        TRec (n, (List.hd beta), typ_subst x s outer t')
      end
    | TApp (t, ts) -> TApp (typ_subst x s outer t, List.map (typ_subst x s outer) ts)
    | TUninit t -> match !t with
      | None -> typ
      | Some t -> typ_subst x s outer t
  and rename_avoid_capture (free : IdSet.t) (ys : id list) (t : typ) =
    let fresh_var old = (* a, b, ... z, aa, bb, ..., zz, ... *)
      let rec try_ascii m n =
        let attempt = String.make m (Char.chr n) in
        if not (List.mem attempt old) then attempt
        else if (n < int_of_char 'z') then try_ascii m (n+1)
        else try_ascii (m+1) (Char.code 'a') in
      try_ascii 1 (Char.code 'a') in
    let (rev_new_ys, substs) =
      List.fold_left (fun (new_ys, substs) y ->
        if not (IdSet.mem y free) then (y::new_ys, substs)
        else
          let x = fresh_var ((IdMapExt.keys substs) @ IdSetExt.to_list free) in
          (x::new_ys, IdMap.add y (TId x) substs))
        ([], IdMap.empty) ys in
    let new_ys = List.rev rev_new_ys in
    let t' = IdMap.fold (fun x s t -> typ_subst (Some x) s (fun x -> x) t) substs t in
    (new_ys, t')

  let subst = typ_subst

  let typ_subst x s t = typ_subst (Some x) s (fun x -> x) t


  (** Decides if two types are syntactically equal. This helps subtyping. *)
  let rec equivalent_typ (env : env) (typ1 : typ) (typ2 : typ) : bool = match (typ1, typ2) with
    | TTop, TTop
    | TBot, TBot -> true
    | TPrim p1, TPrim p2 -> p1 = p2
    | TInter (_, s1, s2), TInter (_, t1, t2)
    | TUnion (_, s1, s2), TUnion (_, t1, t2) -> 
      (equivalent_typ env s1 t1 && equivalent_typ env s2 t2) ||
        (equivalent_typ env s1 t2 && equivalent_typ env s2 t1)
    | TSource (_, s), TSource (_, t)
    | TSink (_, s), TSink (_, t)
    | TRef (_, s), TRef (_, t) -> equivalent_typ env s t
    | TThis _, TThis _ -> true (* ASSUMING THAT THIS TYPES ARE EQUIVALENT *)
    | TApp (s1, s2s), TApp (t1, t2s) ->
      (* for well-kinded types, for_all2 should not signal an error *)
      if (List.length s2s <> List.length t2s) then false
      else equivalent_typ env s1 t1 && List.for_all2 (equivalent_typ env) s2s t2s
    | TId n1, TId n2 ->
      (n1 = n2) ||
        (try
           (match Ext.extract_b (IdMap.find n1 env), Ext.extract_b (IdMap.find n2 env) with
           | BTypBound(t1, k1), BTypBound(t2, k2) -> k1 = k2 && equivalent_typ env t1 t2
           | BTermTyp t1, BTermTyp t2 -> equivalent_typ env t1 t2
           | BEmbed _, BEmbed _ ->
             Ext.equivalent_typ env (Ext.embed_t typ1) (Ext.embed_t typ2)
           | _ -> false)
         with Not_found -> false)
    | TArrow (args1, v1, r1), TArrow (args2, v2, r2) ->
      List.length args1 = List.length args2
      && List.for_all2 (equivalent_typ env) args1 args2
      && equivalent_typ env r1 r2
      && (match v1, v2 with
      | None, None -> true
      | Some v1, Some v2 -> equivalent_typ env v1 v2
      | _ -> false)
    | TRec (_, x, s), TRec (_, y, t) ->
      x = y && equivalent_typ env s t
    | TForall (_, x, s1, s2), TForall (_, y, t1, t2) ->
      x = y && equivalent_typ env s1 t1 && equivalent_typ env s2 t2
    | TRegex pat1, TRegex pat2 ->
      Pat.is_equal pat1 pat2
    | TObject o1, TObject o2 ->
      let flds1 = o1.fields in
      let flds2 = o2.fields in
      List.length flds1 = List.length flds2
      && List.for_all2 (equivalent_typ_fld env) flds1 flds2
      && Pat.is_equal o1.absent_pat o2.absent_pat
    | TFix (_, x1, k1, t1), TFix (_, x2, k2, t2) ->
      x1 = x2 && k1 = k2 && equivalent_typ env t1 t2
    | TLambda (_, args1, t1), TLambda (_, args2, t2) ->
      args1 = args2 && equivalent_typ env t1 t2
    | TUninit t1, TUninit t2 -> begin match !t1, !t2 with
      | None, None -> true
      | Some t1, Some t2 -> equivalent_typ env t1 t2
      | _, _ -> false
    end
    | _, _ -> false

  and equivalent_typ_fld env (pat1, pres1, t1) (pat2, pres2, t2) = 
    Pat.is_equal pat1 pat2 && pres1 = pres2 && equivalent_typ env t1 t2


  (* canonicalize types as best as possible *)
  let rec canonical_type t =
    let c = canonical_type in
    match t with
    | TEmbed t -> TEmbed (Ext.canonical_type t)
    | TBot -> t
    | TTop -> t
    | TPrim _ -> t
    | TRegex _ -> t
    | TId _ -> t
    | TApp(f, args) -> TApp(c f, List.map c args)
    | TLambda(n, yks, t) -> TLambda(n, yks, c t)
    | TUnion (n, _, _) -> begin
      let rec collect t = match t with
        | TUnion (_, t1, t2) -> collect (c t1) @ collect (c t2)
        | _ -> [t] in
      let pieces = collect t in
      let nodups = L.remove_dups pieces in
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
      | TEmbed t1, t2 -> TEmbed(Ext.canonical_type (Ext.embed_t (TInter(n, TEmbed t1, t2))))
      | t1, TEmbed t2 -> TEmbed(Ext.canonical_type (Ext.embed_t (TInter(n, t1, TEmbed t2))))
      | (TForall(_, alpha, bound1, typ1) as t1), (TForall(_, beta, bound2, typ2) as t2) ->
        if equivalent_typ IdMap.empty bound1 bound2
        then TForall(n, alpha, bound1, c (TInter (None, typ1, subst (Some beta) (TId alpha) (fun x -> x) typ2)))
        else TInter(n, t1, t2)
      | t1, t2 -> if t1 = t2 then t1 else TInter(n, t1, t2)
    end
    | TForall (n, alpha, bound, typ) -> TForall(n, alpha, c bound, c typ)
    | TRec (n, alpha, typ) -> TRec(n, alpha, c typ)
    | TArrow (args, var, ret) -> TArrow (map c args, opt_map c var, c ret)
    | _ -> t (* TODO: FINISH THE OTHER TYPES *)



  let rec merge typ flds = match typ with
    | TUnion(n, t1, t2) -> TUnion (n, merge t1 flds, merge t2 flds)
    | TInter(n, t1, t2) -> TInter(n, merge t1 flds, merge t2 flds)
    | TObject o -> begin
      let unionPats = Pat.union (flds.absent_pat) (Pat.unions (map fst3 flds.fields)) in
      let restrict_field (n, p, t) =
        let n' = Pat.subtract n unionPats in
        if (Pat.is_empty n') then None
        else Some (n', p, t) in
      let oldFields = L.filter_map restrict_field o.fields in
      let newFields = oldFields @ flds.fields in
      let newAbsent = Pat.union (Pat.subtract o.absent_pat unionPats) (flds.absent_pat) in
      let newAbsent = if Pat.is_empty newAbsent then Pat.empty else newAbsent in
      let ret = TObject (mk_obj_typ newFields newAbsent) in
      ret
    end
    | TRec(n, id, t) -> TRec(n, id, merge t flds)
    | TRef (n, t) -> TRef (n, merge t flds)
    | TSource (n, t) -> TSource (n, merge t flds)
    | TSink (n, t) -> TSink (n, merge t flds)
    | TThis t -> TThis (merge t flds)
    | _ -> typ

  and lookup_typ env x = match Ext.extract_b (IdMap.find x env) with
    | BTypBound(t, k) -> (t, k)
    | _ -> raise Not_found

  and expose_twith typenv typ = let expose_twith = expose_twith typenv in match typ with
    | TWith (t, flds) ->
      let t = match t with TId x -> (try fst2 (lookup_typ typenv x) with Not_found -> t) | _ -> t in
      let flds' = mk_obj_typ (map (third3 expose_twith) flds.fields) flds.absent_pat in
      replace_name None (merge t flds')
    | TUnion(n, t1, t2) -> TUnion (n, expose_twith t1, expose_twith t2)
    | TInter(n, t1, t2) -> TInter(n, expose_twith t1, expose_twith t2)
    | TRec(n, id, t) -> TRec(n, id, expose_twith t)
    | TRef (n, t) -> TRef (n, expose_twith t)
    | TSource (n, t) -> TSource (n, expose_twith t)
    | TSink (n, t) -> TSink (n, expose_twith t)
    | TThis t -> TThis (expose_twith t)
    | _ -> typ

  and simpl_typ typenv typ = match typ with
    | TEmbed _ -> typ
    | TPrim _ 
    | TUnion _
    | TInter _
    | TRegex _
    | TArrow _
    | TRef _
    | TSource _
    | TSink _
    | TTop _
    | TBot _
    | TLambda _
    | TObject _
    | TId _
    | TThis _
    | TForall _ -> typ
    | TWith(t, flds) -> expose_twith typenv typ
    | TFix (n, x, k, t) -> apply_name n (simpl_typ typenv (subst (Some x) typ (fun x -> x) t))
    | TRec (n, x, t) -> apply_name n (simpl_typ typenv (subst (Some x) typ (fun x -> x) t))
    | TApp (t1, ts) -> 
      begin match expose typenv (simpl_typ typenv t1) with
      | TPrim "Constructing" -> List.hd ts
      | TPrim "Mutable" -> begin
        match ts with
        | [t] -> begin match expose typenv (simpl_typ typenv t) with
          | TRef (n, t) -> TRef (n, t)
          | TSource (n, t) -> TRef (n, t)
          | TSink (n, t) -> TRef (n, t)
          | _ -> raise (Invalid_argument "Expected a TRef, TSoruce or TSink argument to Mutable<T>")
        end
        | _ ->  raise (Invalid_argument "Expected one argument to Mutable<T>")
      end
      | TPrim "Immutable" -> begin
        match ts with
        | [t] -> begin match expose typenv (simpl_typ typenv t) with
          | TRef (n, t) -> TSource (n, t)
          | TSource (n, t) -> TSource (n, t)
          | TSink (n, t) -> TSource (n, t)
          | _ -> raise (Invalid_argument "Expected a TRef, TSoruce or TSink argument to Immutable<T>")
        end
        | _ ->  raise (Invalid_argument "Expected one argument to Mutable<T>")
      end
      | TLambda (n, args, u) -> 
        let name = match n with
          | None -> None
          | Some n ->
            let names = intersperse ", "
              (List.map (fun t -> match name_of t with Some n -> n | None -> string_of_typ t) ts) in
            Some (n ^ "<" ^ (List.fold_right (^) names ">")) in
        apply_name name
          (simpl_typ typenv
             (List.fold_right2 (* well-kinded, no need to check *)
                (fun (x, k) t2 u -> subst (Some x) t2 (fun x -> x) u)
                args ts u))
      | func_t ->
        let msg = sprintf "ill-kinded type application in simpl_typ. Type is \
                           \n%s\ntype in function position is\n%s\n"
          (string_of_typ typ) (string_of_typ func_t) in
        raise (Invalid_argument msg)
    end
    | TUninit t -> match !t with
      | None -> typ
      | Some t -> simpl_typ typenv t

  and expose typenv typ = match typ with
    | TId x -> 
      (try 
        expose typenv (simpl_typ typenv (fst2 (lookup_typ typenv x)))
       with Not_found -> Printf.eprintf "Could not find type %s\n" x; raise Not_found)
    | TThis t -> TThis (expose typenv t)
    | _ -> typ


end



module MakeModule
  (Pat : SET)
  (STROBE : STROBE_ACTIONS with type pat = Pat.t)
  (EXT : EXT_TYP_ACTIONS   
   with type typ = STROBE.extTyp
  with type kind = STROBE.extKind
  with type binding = STROBE.extBinding
  with type baseTyp = STROBE.typ
  with type baseKind = STROBE.kind
  with type baseBinding = STROBE.binding
  with type env = STROBE.env)
 :
  (STROBE_MODULE 
   with type typ = STROBE.typ
  with type kind = STROBE.kind
  with type binding = STROBE.binding
  with type extTyp = STROBE.extTyp
  with type extKind = STROBE.extKind
  with type extBinding = STROBE.extBinding
  with type pat = Pat.t
  with type env = STROBE.env) =
struct
  include STROBE
  module Ext = EXT
  module Pat = Pat
end
