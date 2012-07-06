open Prelude
open Sig
open Strobe_sigs

module L = ListExt


module MakeActions 
  (STROBE : STROBE_MODULE)
  (ExtSub : EXT_TYP_SUBTYPING
   with type typ = STROBE.extTyp
  with type kind = STROBE.extKind
  with type binding = STROBE.extBinding
  with type baseTyp = STROBE.typ
  with type baseKind = STROBE.kind
  with type baseBinding = STROBE.binding
  with type env = STROBE.env)
  (Env : TYP_ENV
   with type typ = ExtSub.typ
  with type kind = ExtSub.kind
  with type binding = ExtSub.binding
  with type env = ExtSub.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
  : (STROBE_SUBTYPING
     with type typ = STROBE.typ
  with type kind = STROBE.kind
  with type binding = STROBE.binding
  with type extTyp = STROBE.extTyp
  with type extKind = STROBE.extKind
  with type extBinding = STROBE.extBinding
  with type pat = STROBE.pat
  with type obj_typ = STROBE.obj_typ
  with type presence = STROBE.presence
  with type env = STROBE.env) =
struct
  include STROBE
  open STROBE



  (* Necessary for equi-recursive subtyping. *)
  module TypPair = struct
    type s = typ * typ
    type t = env * s
    let compare = Pervasives.compare
  end
  module TPMap = Map.Make (TypPair) (* to fix *)
  module TPMapExt = MapExt.Make (TypPair) (TPMap)


  let rec expose_typ env t = match t with
  | TId x -> 
    (try (match IdMap.find x env with BTypBound (t, _) -> expose_typ env t | _ -> None)
     with Not_found -> None)
  | t -> Some t


  let expose_arrow env typ = 
    let clear_id t = match t with TId x -> (try fst2 (lookup_typ env x) with Not_found -> t) | _ -> t in
    let opt_clear_id t = match t with None -> None | Some t -> Some (clear_id t) in
    match typ with
    | TArrow(args, varargs, ret) -> TArrow(map clear_id args, opt_clear_id varargs, clear_id ret)
    | _ -> typ



  let pat_env (env : env) : pat IdMap.t =
    let select_pat_bound (x, bs) = 
      match (L.filter_map (fun b -> match Ext.extract_b b with
      | BTypBound(TRegex p, _) -> Some (x, p)
      | _ -> None) bs) with
      | [xp] -> Some xp
      | _ -> None in
    L.fold_right (fun (x,p) env -> IdMap.add x p env)
      (L.filter_map select_pat_bound (IdMap.bindings env))
      IdMap.empty

  exception Invalid_parent of string

  let rec parent_typ' env flds = match flds with
    | [] -> None
    | ((pat, pres, fld)::flds') -> 
       match Pat.is_subset (pat_env env) proto_pat pat with
      | true -> begin match pres with
        | Present -> begin match expose env (simpl_typ env fld) with
          | TPrim "Null" -> Some (TPrim "Null")
          | TSource (_, p)
          | TRef (_, p) -> Some (expose env (simpl_typ env p))
          | _ -> raise (Invalid_parent ("__proto__ is "^ (string_of_typ fld)))
          end
        | _ -> raise (Invalid_parent ("Looking for field " ^ (Pat.pretty pat) ^ " and __proto__ must be present or hidden"))
        end
      | false -> parent_typ' env flds'

  let rec parent_typ (env : env) typ = 
    match expose env (simpl_typ env typ) with
      | TObject ot -> begin match !(ot.cached_parent_typ) with
        | Some cached ->
          cached
        | None ->
          let computed = parent_typ' env ot.fields in
          ot.cached_parent_typ := Some computed;
          computed
      end
      | TUninit t -> begin match !t with
        | None -> raise (Invalid_argument "parent_typ expects TObject")
        | Some t -> parent_typ env t
      end
      | _ -> raise (Invalid_argument "parent_typ expects TObject")

  let rec calc_inherit_guard_pat (env : env) (t : typ) : pat =
    match t with
      | TObject ot ->
          begin match parent_typ env t with
            | None
            | Some (TPrim "Null") ->
              let f (pat, pres, _) = match pres with
                | Inherited
                | Present -> Some pat
                | Maybe _ -> None in
              Pat.unions (L.filter_map f ot.fields)
            | Some (TObject _) ->
              Pat.unions (ot.absent_pat::(L.map fst3 ot.fields))
            | Some pt ->
              raise (Invalid_argument 
                 ("invalid parent type in object type: " ^
               (string_of_typ pt)))
          end
      | TUninit t -> begin match !t with
        | None -> raise (Invalid_argument "calc_inherit_guard_pat expects TObject")
        | Some t -> calc_inherit_guard_pat env t
      end
      | t -> raise (Invalid_argument "expected TObject")

  let rec inherit_guard_pat env typ = match typ with
    | TObject ot -> begin match !(ot.cached_guard_pat) with
      | None -> let pat = calc_inherit_guard_pat env typ in
                ot.cached_guard_pat := Some pat;
                pat
      | Some pat -> pat
    end
    | TUninit t -> begin match !t with
      | None -> raise (Invalid_argument "inherit_guard_pat expects TObject, got TUninit None")
      | Some t -> inherit_guard_pat env t
    end
    | t -> 
      Printf.eprintf "ERROR: Expected object type, got:\n%s\n" (string_of_typ t);
      raise (Invalid_argument ("expected object type, got " ^
                                  (string_of_typ t)))

  let maybe_pats ot = 
    let f (pat, pres, _) acc = match pres with
      | Maybe -> Pat.union pat acc
      | _ -> acc in
    L.fold_right f ot.fields ot.absent_pat


  let cache_hits = ref 0
  let cache_misses = ref 0
  let num_cache_hits () = !cache_hits
  let num_cache_misses () = !cache_misses

  let rec simpl_lookup p (env : env) (t : typ) (pat : pat) : typ =
    (* TODO: it's okay to overlap with a maybe, but not a hidden field;
       inherit_guard_pat does not apply *)
    match t with
    | TObject ot -> 
      let guard_pat = Pat.unions (map fst3 ot.fields) in
      if Pat.is_subset (pat_env env) pat guard_pat then
        let sel (f_pat, _, f_prop) =
          if Pat.is_overlapped f_pat pat then Some f_prop
          else None in
        L.fold_right (fun s t -> typ_union env s t)
          (L.filter_map sel ot.fields)
          TBot
      else
        raise (Typ_error (p, FixedString "simpl_lookup: checking for a hidden or absent field"))
    | TUninit t -> begin match !t with
      | None -> raise (Invalid_argument "simpl_lookup expects TObject")
      | Some t -> simpl_lookup p env t pat
    end
    | _ -> raise (Typ_error (p, FixedString "simpl_lookup: object expected"))

  and inherits p (env : env) (orig_t : typ) (pat : pat) : typ =
    try
      let t = expose env (simpl_typ env orig_t) in
      if Pat.is_subset (pat_env env) pat (inherit_guard_pat env t) then
        begin match t with
        | TObject ot -> 
          let sel (f_pat, _, f_prop) =
            if Pat.is_overlapped f_pat pat then Some f_prop
            else None in
          L.fold_right (fun s t -> typ_union env s t)
            (L.filter_map sel ot.fields)
            (match parent_typ env t with
            | None
            | Some (TPrim "Null") -> TBot
            | Some parent_typ -> 
              if (equivalent_typ env orig_t (expose env (simpl_typ env parent_typ))) 
              then orig_t
              else begin
                let check_parent_pat = (Pat.intersect pat (maybe_pats ot)) in
                (* Printf.printf "pat: %s\nmaybe_pat:%s\nintersect: %s\norig_t: %s\nparent_typ:%s\n\n" (Pat.pretty pat) (Pat.pretty (maybe_pats ot)) (Pat.pretty check_parent_pat) (string_of_typ orig_t)(string_of_typ (expose env (simpl_typ env parent_typ))); *)
                inherits p env parent_typ check_parent_pat
              end
            )
        | TUninit t -> begin match !t with
          | None -> raise (Invalid_argument "inherits expects TObject")
          | Some t -> inherits p env t pat
        end
        | _ -> failwith "lookup non-object"
        end
      else begin match parent_typ env t with
      | Some (TPrim "Null") -> TPrim "Undef"
      | _ ->
        raise (Typ_error (p, (PatTyp((fun p t -> sprintf "lookup hidden field with %s in:\n%s" (Pat.pretty p) 
          (string_of_typ t)), pat, orig_t))))
      end
    with Invalid_parent msg -> raise (Typ_error (p, FixedString msg))

  and subt env cache s t =
    trace "STROBE_subt" (string_of_typ s ^ " <?: " ^ string_of_typ t) snd2 (fun () -> subt' env cache s t)
  and subt' (env : env) (cache : bool TPMap.t) s t : bool TPMap.t * bool = 
    let open TypPair in
    let (|||) c thunk = if (snd c) then c else thunk (fst c) in
    let (&&&) c thunk = if (snd c) then thunk (fst c) else c in
    let subtype_typ_list c t1 t2 = c &&& (fun c -> subt env c t1 t2) in
    let addToCache (cache, ret) = (TPMap.add ((* project_typs t1 t2 *) env, (s, t)) ret cache, ret) in
    try incr cache_hits; (cache, TPMap.find ((* project_typs s t  *)env, (s, t)) cache)
    with Not_found -> begin decr cache_hits; incr cache_misses; addToCache (if s = t then (cache, true)
      else if equivalent_typ env s t then cache, true
      else match s, t with
      | TApp(sf, sargs), TApp(tf, targs) ->
        (cache, sf = tf) &&& (fun c -> List.fold_left2 subtype_typ_list (c, true) sargs targs)
      | TEmbed s, TEmbed t -> cache, ExtSub.subtype env s t
      | _ ->
        (* let _ = Printf.eprintf "Not equivalent, so simplfying.\n" in *)
        let simpl_s = expose env (simpl_typ env s) in
        let simpl_t = expose env (simpl_typ env t) in
        (* Printf.eprintf "Is %s <?: %s?\n" (string_of_typ simpl_s) (string_of_typ simpl_t); *)
        try (cache, TPMap.find ((* project_type simpl_s simpl_t *) env, (simpl_s, simpl_t)) cache)
        with Not_found ->
          (* Printf.printf "Checking %s against %s\n" (string_of_typ simpl_s) (string_of_typ simpl_t); *)
          let cache = TPMap.add (env, (s, t)) true cache in
          match simpl_s, simpl_t with
          | TUninit t', t2 -> begin match !t' with
            | None -> subt env cache (TPrim "Undef") t2
            | Some t1 -> subt env cache t1 t2
          end
          | t1, TUninit t' -> begin match !t' with
            | None -> subt env cache t1 (TPrim "Undef")
            | Some t2 -> subt env cache t1 t2
          end
          | TEmbed t1, t2 -> cache, ExtSub.subtype env t1 (Ext.embed_t t2)
          | t1, TEmbed t2 -> cache, ExtSub.subtype env (Ext.embed_t t1) t2
          | TRegex pat1, TRegex pat2 ->
            (* Printf.eprintf "TREGEX: Is %s <?: %s?   " (Pat.pretty pat1) (Pat.pretty pat2); *)
            let ret = Pat.is_subset (pat_env env) pat1 pat2 in
            (* Printf.eprintf "%b\n" ret; *)
            (cache, ret)
          | TUnion(_, t11, t12), t2 -> (* order matters -- left side must be split first! *)
            subt env cache t11 t2 &&& (fun c -> subt env c t12 t2)
          | t1, TUnion(_, t21, t22) ->
            subt env cache t1 t21 ||| (fun c -> subt env c t1 t22)
          | t1, TInter(_, t21, t22) -> (* order matters -- right side must be split first! *)
            subt env cache t1 t21 &&& (fun c -> subt env c t1 t22)
          | TInter(_, t11, t12), t2 ->
            subt env cache t11 t2 ||| (fun c -> subt env c t12 t2)
          | _, TThis(TPrim "Unsafe") -> cache, true (* Can always mask the this parameter as Unsafe *)
          | TPrim "Null", TRef (_, TObject _)
          | TPrim "Null", TSource (_, TObject _)
          | TPrim "Null", TSink (_, TObject _) -> cache, true (* null should be a subtype of all object types *)
          | TThis (TId _ as id), t -> subt env cache (TThis (expose env id)) t
          | t, TThis(TRec _ as r) -> subt env cache t (TThis (expose env r))
          | TThis (TRef (_, s)), TThis (TRef (_, t))
          | TThis (TRef (_, s)), TThis (TSource (_, t))
          | TThis (TRef (_, s)), TThis (TSink (_, t))
          | TThis (TSource (_, s)), TThis (TRef (_, t))
          | TThis (TSource (_, s)), TThis (TSource (_, t))
          | TThis (TSource (_, s)), TThis (TSink (_, t))
          | TThis (TSink (_, s)), TThis (TRef (_, t))
          | TThis (TSink (_, s)), TThis (TSource (_, t))
          | TThis (TSink (_, s)), TThis (TSink (_, t))
          | TRef (_, s), TThis (TRef (_, t))
          | TRef (_, s), TThis (TSource (_, t))
          | TRef (_, s), TThis (TSink (_, t))
          | TSource (_, s), TThis (TRef (_, t))
          | TSource (_, s), TThis (TSource (_, t))
          | TSource (_, s), TThis (TSink (_, t))
          | TSink (_, s), TThis (TRef (_, t))
          | TSink (_, s), TThis (TSource (_, t))
          | TSink (_, s), TThis (TSink (_, t)) -> subt env cache s t (* ONLY HAVE TO GO ONE WAY ON THIS TYPES *)
          | TThis _, TThis _ -> cache, false
          | _, TThis t2 -> subt env cache s t2
          | TThis t1, _ -> subt env cache t1 t
          | TArrow (args1, None, ret1), TArrow (args2, Some var2, ret2) ->
            if (List.length args1 < List.length args2) then (cache, false)
            else 
              let args2' = L.fill (List.length args1 - List.length args2) var2 args2 in
              (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2') (ret2::args1))
          | TArrow (args1, Some var1, ret1), TArrow (args2, None, ret2) ->
            if (List.length args1 > List.length args2) then (cache, false)
            else 
              let args1' = L.fill (List.length args2 - List.length args1) var1 args1 in
              (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2) (ret2::args1'))
          | TArrow (args1, Some var1, ret1), TArrow (args2, Some var2, ret2) ->
            if (List.length args1 > List.length args2) then
              let args2' = L.fill (List.length args1 - List.length args2) var2 args2 in
              (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2') (ret2::args1))
            else 
              let args1' = L.fill (List.length args2 - List.length args1) var1 args1 in
              (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2) (ret2::args1'))
          | TId n1, t2 when t2 = TId n1 -> cache, true (* SA-Refl-TVar *)
          | TId n1, _ -> (* SA-Trans-TVar *)
            (try
               let (s, _) = lookup_typ env n1 in subt env cache s t
             with Not_found -> cache, false)
          (* NOT SOUND? *)
          (* | t, TId x ->  *)
          (*   (try *)
          (*      subt env cache t (fst2 (lookup_typ env x)) *)
          (*    with Not_found -> Printf.printf "Cannot find %s in environment\n" x; raise Not_found) *)
          | TObject obj1, TObject obj2 ->
            subtype_object env cache obj1 obj2
          | TRef (_, s'), TRef (_, t') -> subt env cache s' t' &&& (fun c -> subt env c t' s')
          | TSource (_, s), TSource (_, t) -> subt env cache s t
          | TSink (_, s), TSink (_, t) -> subt env cache t s
          | TRef (_, s), TSource (_, t) -> subt env cache s t
          | TRef (_, s), TSink (_, t) -> subt env cache t s
          | TForall (_, x1, s1, t1), TForall (_, x2, s2, t2) -> 
            (* Kernel rule *)
            (* TODO: ensure s1 = s2 *)
            subt env cache s1 s2 &&& (fun c -> subt env c s2 s1) &&&
              (fun c ->
                let t2 = subst (Some x2) (TId x1) (fun x -> x) t2 in
                let env' = Env.bind_typ_id x1 (Ext.embed_t s1) env in
                subt env' c t1 t2)
          | _, TTop -> cache, true
          | TBot, _ -> cache, true
          | TLambda (_, [(x, KStar)], s), TLambda (_, [(y, KStar)], t) ->
            let env = Env.bind_typ_id x (Ext.embed_t TTop) env in
            let env = Env.bind_typ_id y (Ext.embed_t TTop) env in
            subt env cache s t
          | _ -> cache, false)
    end

  (* Check that an "extra" field is inherited *)
  and check_inherited env cache lang other_proto typ =
    subt env cache typ (inherits Pos.dummy env other_proto lang)

  and subtype_presence prop1 prop2 = match prop1, prop2 with
    | Present, Present 
    | Maybe, Maybe
    | Inherited, Inherited
    | Present , Maybe
    | Present, Inherited -> true
    | _, _ -> false

  and subtype_object env cache obj1 obj2 : bool TPMap.t * bool =
    trace "STROBE_subtype_OBJECT" "" snd2 (fun () -> subtype_object' env cache obj1 obj2)
  and subtype_object' env cache obj1 obj2 : bool TPMap.t * bool =
    let (&&&) c thunk = if (snd c) then thunk (fst c) else c in
    let subtype_typ_list f c x = c &&& (fun c -> f c x) in
    let lhs_absent = absent_pat obj1 in
    let rhs_absent = absent_pat obj2 in
    let check_simple_overlap cache ((pat1, pres1, t1), (pat2, pres2, t2)) = 
      if Pat.is_overlapped pat1 pat2 then
        begin
          (cache, subtype_presence pres1 pres2) &&&
            (* Printf.printf "%s overlaps %s; checking subtypes of %s <: %s\n" *)
            (*   (Pat.pretty pat1) (Pat.pretty pat2) (string_of_typ t1) (string_of_typ t2); *)
            (fun c -> subt env c t1 t2)
        end
      else
        cache, true in
    let check_pat_containment () =
      try
        (if not (Pat.is_subset (pat_env env) (possible_field_cover_pat obj2) 
                   (cover_pat obj1)) then
            match Pat.example (Pat.subtract (possible_field_cover_pat obj2)
                               (cover_pat obj1)) with
            | Some ex -> failwith ("fields on the RHS that are not on the LHS, e.g. " ^ ex ^ 
                                      "; cover_pat obj1 = " ^ (Pat.pretty (cover_pat obj1)) ^
                                      "; possible_pat obj1 = " ^ (Pat.pretty (possible_field_cover_pat obj1)))
            | None -> failwith "error building counterexample for (2)");
        (if not (Pat.is_subset (pat_env env) rhs_absent lhs_absent); 
         then failwith "subtype_object: violated 2-2");
        true
      with _ -> false in
    let check_lhs_absent_overlap cache (rhs_pat, rhs_pres, rhs_prop) = 
      cache, if Pat.is_overlapped rhs_pat lhs_absent then
        match rhs_pres with
          | Maybe | Inherited -> true
          | _ -> false
      else true in
    let check_rhs_inherited cache (rhs_pat, rhs_pres, rhs_typ) = 
      match rhs_pres with
      | Inherited -> 
          let lhs_typ = inherits Pos.dummy env (TObject obj1) rhs_pat in
          subt env cache lhs_typ rhs_typ
      | _ -> cache, true in
    let (cache, rest) = 
      L.fold_left (subtype_typ_list check_simple_overlap) (cache, true) (L.pairs obj1.fields obj2.fields) in
    (cache, rest && check_pat_containment ()) &&& 
      (fun c -> L.fold_left (subtype_typ_list check_lhs_absent_overlap) (c, true) obj2.fields) &&&
      (fun c -> L.fold_left (subtype_typ_list check_rhs_inherited) (c, true) obj2.fields)

  and subtypes env ss ts = 
    let (&&&) c thunk = if (snd c) then thunk (fst c) else c in
    try 
      let (c, r) = List.fold_left2 (fun c s t -> c &&& (fun c -> subt env c s t)) (!cache, true) ss ts in
      cache := c;
      r
    with 
      | Invalid_argument _ -> false (* unequal lengths *)

  and cache : bool TPMap.t ref = ref TPMap.empty 
  and print_cache lbl =
    let open TypPair in
    let open Format in
    let open FormatExt in
    let cut fmt = Format.pp_print_cut fmt () in
    TPMapExt.p_map lbl cut
      (fun (env, (t1, t2)) -> 
        pair
          (label_braces "Env: " cut [Env.print_env env])
          (pair (Pretty.typ t1) (Pretty.typ t2)))
      (fun b -> text (string_of_bool b))
      !cache

  and subtype env s t = 
    let (c, r) = subt env !cache s t in
    cache := c;
    r

  and typ_union cs s t = match subtype cs s t, subtype cs t s with
      true, true -> s (* t = s *)
    | true, false -> t (* s <: t *)
    | false, true -> s (* t <: s *)
    | false, false -> TUnion (None, s, t)

  and typ_intersect cs s t = match subtype cs s t, subtype cs t s with
    | true, true -> s
    | true, false -> s (* s <: t *)
    | false, true -> t
    | false, false -> TInter (None, s, t)

  let filter_typ (pred : typ -> bool) (typ : typ) = 
    let none_removed = ref true in
    let rec union (typs : typ list) n = match typs with
      | t1 :: ts -> fold_right (fun s t -> TUnion (n, s, t)) ts t1
      | _ -> failwith "expected non-empty list" in
    let combine n m = if n = None then m else n in
    let rec f t n_outer : typ list * string option = match t with
      | TUnion (n, s1, s2) -> 
        let n' = combine n n_outer in 
        let (fs1, n1) = f s1 n' in
        let (fs2, n2) = f s2 n' in
        (fs1 @ fs2, combine n' (combine n1 n2))
      | TInter (n, s1, s2) -> 
        let n' = combine n n_outer in
        begin match f s1 n', f s2 n' with
        | ([], n1), ([], n2) -> [], combine n' (combine n1 n2)
        | ([], n1), (typs, n2)
        | (typs, n1), ([], n2) -> typs, combine n' (combine n1 n2)
        | (typs1, n1), (typs2, n2) -> [TInter (n', union typs1 n1, union typs2 n2)], combine n' (combine n1 n2)
        end
      | _ -> if pred t then 
          [t], None
        else 
          begin
            none_removed := false;
            [], None
          end in
    let (typ_lst, _) = f typ None in
    (typ_lst, !none_removed)

  let is_object_typ t = match t with
    | TObject _ -> true
    | TUninit t -> begin match !t with
      | Some (TObject _) -> true
      | _ -> false
    end
    | _ -> false

  let object_typs (typ : typ) : typ list * bool = filter_typ is_object_typ typ
  
end



(* module MakeStrobeTypSub *)
(*   (Strobe : STROBE_TYPS) *)
(*   (Ext : EXT_TYP_SIG with type baseTyp = Strobe.typ with type typ = Strobe.extTyp with type baseKind = Strobe.kind with type kind = Strobe.extKind) *)
(*   (ExtSub : TYP_SUB with type typ = Strobe.extTyp with type kind = Strobe.extKind) *)
(*   : (TYP_SUB with type typ = Strobe.typ with type kind = Strobe.kind) = *)
(* struct *)
(*   type typ = Strobe.typ *)
(*   type kind = Strobe.kind *)
(*   let subtype t1 t2 = match t1, t2 with *)
(*     | Strobe.TEmbed t1, Strobe.TEmbed t2 -> ExtSub.subtype t1 t2 *)
(*     | Strobe.TEmbed t1, _ -> ExtSub.subtype t1 (Ext.embed_t t2) *)
(*     | _, Strobe.TEmbed t2 -> ExtSub.subtype (Ext.embed_t t1) t2 *)
(*     | _, _ -> t1 = t2 *)
(* end *)
