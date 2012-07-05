open Prelude
open Sig

open JQuery_sigs
open Strobe_sigs

module Make : JQUERY_TYP = functor (Css : Css.CSS) -> functor (STROBE : TYPS) -> struct
  module Css = Css
  type sel = Css.t

  type baseKind = STROBE.kind
  type kind = 
    | KMult of kind
    | KStrobe of baseKind

  type baseTyp = STROBE.typ
  type typ = 
    | TForall of string option * id * sigma * typ
    | TApp of typ * sigma list
    | TDom of string option * typ * sel
    | TStrobe of STROBE.typ

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


  type baseBinding = STROBE.binding
  type binding = BStrobe of baseBinding | BMultBound of multiplicity * kind

  type env = binding list IdMap.t
end

module MakeActions
  (Strobe : STROBE_ACTIONS)
  (JQ : JQUERY_TYPS 
   with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env)
  (Css : Css.CSS with type t = JQ.sel)
  : (JQUERY_ACTIONS 
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


  let rec embed_t t =
    match t with Strobe.TEmbed (TStrobe t) -> embed_t t | Strobe.TEmbed t -> t | t -> TStrobe t
  let rec embed_k k =
    match k with Strobe.KEmbed (KStrobe k) -> embed_k k | Strobe.KEmbed k -> k | k -> KStrobe k
  let rec embed_b b =
    match b with Strobe.BEmbed (BStrobe b) -> embed_b b | Strobe.BEmbed b -> b | b -> BStrobe b
  let rec extract_t t =
    match t with TStrobe (Strobe.TEmbed t) -> extract_t t | TStrobe t -> t | t -> Strobe.TEmbed t
  let rec extract_k k =
    match k with KStrobe (Strobe.KEmbed k) -> extract_k k | KStrobe k -> k | k -> Strobe.KEmbed k
  let rec extract_b b =
    match b with BStrobe (Strobe.BEmbed b) -> extract_b b | BStrobe b -> b | b -> Strobe.BEmbed b
  let rec unwrap_bt t =
    match t with Strobe.TEmbed (TStrobe t) -> unwrap_bt t | _ -> t
  let rec unwrap_bk k =
    match k with Strobe.KEmbed (KStrobe k) -> unwrap_bk k | _ -> k
  let rec unwrap_bb b =
    match b with Strobe.BEmbed (BStrobe b) -> unwrap_bb b | _ -> b
  let rec unwrap_t t =
    match t with TStrobe (Strobe.TEmbed t) -> unwrap_t t | _ -> t
  let rec unwrap_k k =
    match k with KStrobe (Strobe.KEmbed k) -> unwrap_k k | _ -> k
  let rec unwrap_b b =
    match b with BStrobe (Strobe.BEmbed b) -> unwrap_b b | _ -> b

  let num_typ_errors = ref 0

  let error_on_mismatch = ref false

  let with_typ_exns thunk =
    let prev = !error_on_mismatch in
    error_on_mismatch := true;
    let r = thunk () in
    error_on_mismatch := prev;
    r

  let get_num_typ_errors () = !num_typ_errors

  let rec apply_name n typ = match typ with
    | TStrobe t -> embed_t (Strobe.apply_name n t)
    | TForall(None, x, t, b) -> TForall(n, x, t, b)
    | TDom(None, t, sel) -> TDom(n, t, sel)
    | _ -> typ

  and name_of typ =  match typ with
    | TStrobe t -> Strobe.name_of t
    | TForall(name, _, _, _) -> name
    | TDom(name, _, _) -> name
    | _ -> None

  and replace_name n typ = match typ with
    | TStrobe t -> embed_t (Strobe.replace_name n t)
    | TForall(_, x, t, b) -> TForall(n, x, t, b)
    | TDom(_, t, sel) -> TDom(n, t, sel)
    | _ -> typ


  (* pretty printing *)
  module Pretty = struct
    open Format
    open FormatExt

    let useNames, shouldUseNames =
      let _useNames = ref true in
      let useNames b = _useNames := b in
      let shouldUseNames () = !_useNames in
      useNames, shouldUseNames

    let rec kind k = match k with
      | KStrobe k -> (if shouldUseNames () then squish else label_angles "KSTROBE" cut) [Strobe.Pretty.kind k]
      | KMult m -> label_angles "M" empty [kind m]


    let rec typ t = typ' false t
    and typ' horzOnly t =
      let typ = typ' horzOnly in
      let namedType name fmt =
        if shouldUseNames ()
        then match name with None -> fmt | Some n -> text n
        else match name with None -> horz [text "Unnamed"; fmt] | Some n -> horz [text "Named"; text n; fmt] in
      match t with
      | TStrobe t -> (if shouldUseNames () then squish else label_angles "STROBE" empty) [Strobe.Pretty.typ t]
      | TForall (name, alpha, bound, body) -> begin
        let binding = match bound with
          | STyp t when extract_t t = Strobe.TTop -> text alpha
          | STyp t -> horz [text alpha; text "<:"; typ t]
          | SMult m -> horz [text alpha; text "<:"; multiplicity m]
        in
        namedType name (horzOrVert [horz [text "Forall"; binding; text "."];
                                    typ body])
      end
      | TApp (t, ts) ->
        (match ts with
        | [] -> horz [typ t; text "<>"]
        | _ -> parens [squish [typ t; angles (intersperse (text ",") (map sigma ts))]])
      | TDom (name, t, sel) ->
        namedType name (horzOrVert [horz [typ t; text "@"]; Css.p_css sel])
    and multiplicity m =
      let p = multiplicity in
      match m with
      | MPlain t -> typ t
      | MId name -> squish [text "`"; text name]
      | MZero m -> label_angles "0" empty [p m]
      | MOne m -> label_angles "1" empty [p m]
      | MZeroOne m -> label_angles "01" empty [p m]
      | MOnePlus m -> label_angles "1+" empty [p m]
      | MZeroPlus m -> label_angles "0+" empty [p m]
      | MSum(m1, m2) -> label_angles "Sum" empty [horz[p m1; text "++"]; p m2]
    and sigma s = match s with
      | STyp t -> typ t
      | SMult m -> multiplicity m


    let env (env : env) =
      if IdMap.cardinal env = 0 then [text "No bounded mult variables"] else
      let partition_env e = 
        IdMap.fold
          (fun i bs (other, mults) -> 
            List.fold_left (fun (other, mults) b -> match embed_b (extract_b b) with
            | BStrobe b' ->
              let bs' = try IdMap.find i other with Not_found -> [] in
              (IdMap.add i (embed_b b'::bs') other, mults)
            | BMultBound(m, k) -> (other, IdMap.add i (m, k) mults)) (other, mults) bs)
          e (IdMap.empty, IdMap.empty) in
      let (other, mult_ids) = partition_env env in
      let other_print = Strobe.Pretty.env other in
      let mults = IdMapExt.p_map "Bounded mult variables: " cut
        text
        (fun (m, k) -> 
          horzOrVert [multiplicity m;
                      horz [text "::"; kind k]]) mult_ids in
      add_sep_between (text ",") (other_print @ [mults])
  end
  let string_of_typ = FormatExt.to_string Pretty.typ
  let string_of_mult = FormatExt.to_string Pretty.multiplicity
  let string_of_kind = FormatExt.to_string Pretty.kind

  (* free type variables *)
  let rec free_typ_ids t = match t with
    | TDom(_, t, _) -> free_typ_ids t
    | TForall (_, alpha, bound, typ) ->
      IdSet.remove alpha (IdSet.union (free_sigma_typ_ids bound) (free_typ_ids typ))
    | TApp (t, ss) -> IdSetExt.unions (free_typ_ids t :: (map free_sigma_typ_ids ss))
    | TStrobe t -> Strobe.free_typ_ids t
  and free_sigma_typ_ids s = match s with
    | STyp t -> free_typ_ids t
    | SMult m -> free_mult_typ_ids m
  and free_mult_typ_ids m = match m with
    | MPlain t -> free_typ_ids t
    | MId _ -> IdSet.empty
    | MZero m
    | MOne m
    | MZeroOne m
    | MOnePlus m
    | MZeroPlus m -> free_mult_typ_ids m
    | MSum(m1, m2) -> IdSet.union (free_mult_typ_ids m1) (free_mult_typ_ids m2)

  let rec free_mult_ids m = match m with
    | MPlain t -> free_typ_mult_ids t
    | MId name -> IdSet.singleton name
    | MZero m
    | MOne m
    | MZeroOne m
    | MOnePlus m
    | MZeroPlus m -> free_mult_ids m
    | MSum(m1, m2) -> IdSet.union (free_mult_ids m1) (free_mult_ids m2)
  and free_typ_mult_ids t = match t with
    | TDom(_, t, _) -> free_typ_ids t
    | TForall (_, alpha, bound, typ) ->
      IdSet.union (free_sigma_mult_ids bound) (free_typ_ids typ)
    | TApp (t, ss) -> IdSetExt.unions (free_typ_ids t :: (map free_sigma_typ_ids ss))
    | TStrobe t -> Strobe.map_reduce_t free_typ_mult_ids IdSet.union IdSet.empty t
  and free_sigma_mult_ids s = match s with
    | STyp t -> free_typ_ids t
    | SMult m -> free_mult_typ_ids m
      
  let free_ids t = IdSet.union (free_typ_ids t) (free_typ_mult_ids t)

  let free_sigma_ids s = (free_sigma_typ_ids s, free_sigma_mult_ids s)

  let rec rename_avoid_capture (free : IdSet.t) (ys : id list) (t : typ) =
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
          (x::new_ys, IdMap.add y (STyp (embed_t (Strobe.TId x))) substs))
        ([], IdMap.empty) ys in
    let new_ys = List.rev rev_new_ys in
    let t' = IdMap.fold subst substs (STyp t) in
    let t'' = match t' with STyp t -> t | _ -> failwith "impossible" in
    (new_ys, t'')

  and subst x (s : sigma) (sigma : sigma) : sigma =
    let rec sigma_help sigma : sigma = match sigma with
      | STyp typ -> STyp (typ_help typ)
      | SMult mult -> SMult (mult_help mult)
    and mult_help mult : multiplicity = match mult with
      | MPlain typ -> plain_help typ
      | MId y -> if x = y then (Printf.eprintf "got here?\n"; match s with SMult m -> m | STyp _ -> mult) else mult
      | MZero m -> MZero (mult_help m)
      | MOne m -> MOne (mult_help m)
      | MZeroOne m -> MZeroOne (mult_help m)
      | MOnePlus m -> MOnePlus (mult_help m)
      | MZeroPlus m -> MZeroPlus (mult_help m)
      | MSum (m1, m2) -> MSum (mult_help m1, mult_help m2)
    and plain_help typ : multiplicity = match typ with
      | TStrobe (Strobe.TId y) -> 
        if y = x 
        then match s with
        | STyp t -> MPlain t
        | SMult m -> m
        else MPlain typ
      | _ -> MPlain (typ_help typ)
    and typ_help typ : typ = match typ with
      | TStrobe tstrobe -> begin
        let subst_t = match s with
          | STyp t -> embed_t (Strobe.subst (Some x) (extract_t t) typ_help tstrobe)
          | SMult m -> embed_t (Strobe.subst None Strobe.TTop typ_help tstrobe)
        in unwrap_t subst_t
      end
      | TApp(f, args) -> TApp(typ_help f, List.map sigma_help args)
      | TForall (name, alpha, bound, body) -> if x = alpha then typ else
          let (free_t, free_m) = free_sigma_typ_ids s, free_sigma_mult_ids s in
          let (beta, body') = rename_avoid_capture (IdSet.union free_t free_m) [alpha] body in
          TForall (name, (List.hd beta), sigma_help bound, typ_help body')
      | TDom (name, t, sel) -> TDom(name, typ_help t, sel)
    in sigma_help sigma

  let typ_typ_subst x t typ = match subst x (STyp t) (STyp typ) with STyp t -> t | _ -> failwith "impossible"
  let typ_mult_subst x t m = match subst x (STyp t) (SMult m) with SMult m -> m | _ -> failwith "impossible"
  let mult_typ_subst x m t = match subst x (SMult m) (STyp t) with STyp t -> t | _ -> failwith "impossible"
  let mult_mult_subst x m mult = match subst x (SMult m) (SMult mult) with SMult m -> m | _ -> failwith "impossible"




  (* simple structural equivalence -- e.g. up to permutation of parts of Union or Inter or Sum
   * and can be extended to objects later... *)
  let rec equivalent_sigma (env : env) s1 s2 =
    match s1, s2 with
    | STyp t1, STyp t2 -> equivalent_typ env t1 t2
    | SMult m1, SMult m2 -> equivalent_multiplicity env m1 m2
    | _ -> false
  and equivalent_typ env t1 t2 = match t1, t2 with
    | TForall(_, alpha, s1, t1), TForall(_, beta, s2, t2) ->
      equivalent_sigma env s1 s2 && (match s1 with
      | SMult _ -> equivalent_typ env t1 (mult_typ_subst beta (MId alpha) t2)
      | STyp _ -> equivalent_typ env t1 (typ_typ_subst beta (embed_t (Strobe.TId alpha)) t2))
    (* | TLambda(_, args1, ret1), TLambda(_, args2, ret2) -> *)
    (*   if (List.length args1 <> List.length args2) then false *)
    (*   else if not (List.for_all2 (fun (_, k1) (_, k2) -> k1 = k2) args1 args2) then false *)
    (*   else *)
    (*     let ret2 = List.fold_left2 (fun r (x1,k1) (x2,k2) -> *)
    (*       match k1 with *)
    (*       | KMult _ -> mult_typ_subst x2 (MId x1) r *)
    (*       | _ -> typ_typ_subst x2 (TId x1) r) ret2 args1 args2 *)
    (*     in equivalent_typ env ret1 ret2 *)
    | TApp(t1, args1), TApp(t2, args2) ->
      if (List.length args1 <> List.length args2) then false
      else equivalent_typ env t1 t2 && List.for_all2 (equivalent_sigma env) args1 args2
    | TDom(_, t1, sel1), TDom(_, t2, sel2) ->
      equivalent_typ env t1 t2 && Css.is_equal sel1 sel2
    | TStrobe (Strobe.TEmbed t1), _ -> equivalent_typ env t1 t2
    | _, TStrobe (Strobe.TEmbed t2) -> equivalent_typ env t1 t2
    | TStrobe t1, TStrobe t2 -> Strobe.equivalent_typ env t1 t2
    | _ -> false
  and equivalent_multiplicity env m1 m2 = match m1, m2 with
    | MPlain t1, MPlain t2 -> equivalent_typ env t1 t2
    | MId n1, MId n2 ->
      (n1 = n2) ||
        (try
           (match IdMap.find n1 env, IdMap.find n2 env with
           | [BStrobe (Strobe.BTypBound(t1, k1))], [BStrobe (Strobe.BTypBound(t2, k2))] -> 
             k1 = k2 && equivalent_typ env (embed_t t1) (embed_t t2)
           | [BStrobe (Strobe.BTermTyp t1)], [BStrobe (Strobe.BTermTyp t2)] -> equivalent_typ env (embed_t t1) (embed_t t2)
           | [BMultBound(m1, k1)], [BMultBound(m2, k2)] -> k1 = k2 && equivalent_multiplicity env m1 m2
           | _ -> false)
         with Not_found -> false)
    | MZero m1, MZero m2
    | MOne m1, MOne m2
    | MZeroOne m1, MZeroOne m2
    | MOnePlus m1, MOnePlus m2
    | MZeroPlus m1, MZeroPlus m2 -> equivalent_multiplicity env m1 m2
    | MSum(m11, m12), MSum(m21, m22) ->
      (equivalent_multiplicity env m11 m21 && equivalent_multiplicity env m12 m22) ||
        (equivalent_multiplicity env m11 m22 && equivalent_multiplicity env m12 m21)
    | _ -> false

  (* canonical forms *)
  let rec canonical_sigma s = match s with
    | STyp t -> STyp (canonical_type t)
    | SMult m -> SMult (canonical_multiplicity m)

  and canonical_type t =
    let module S = Strobe in
    let c = canonical_type in
    let c'' t = c (embed_t t) in
    let c' t = extract_t (c'' t) in
    let t = unwrap_t t in
    match t with
    | TApp(f, args) -> TApp(c f, List.map canonical_sigma args)
    | TStrobe(S.TUnion (n, _, _)) -> begin
      let rec collect t = match unwrap_t t with
        | TStrobe(S.TUnion (_, t1, t2)) -> collect (c (embed_t t1)) @ collect (c (embed_t t2))
        | TStrobe(S.TEmbed t) -> failwith "impossible: embed_t should've removed this case"
        | TStrobe t -> [unwrap_bt t]
        | _ -> [extract_t t] in
      let pieces = collect t in
      let nodups = remove_dups pieces in
      match List.rev nodups with
      | [] -> failwith "impossible"
      | hd::tl -> 
        embed_t (S.apply_name n (List.fold_left (fun acc t ->
                     if t = S.TBot
                     then acc 
                     else S.TUnion(None, t, acc)) hd tl))
    end
    | TStrobe(S.TInter (n, t1, t2)) -> begin
      match unwrap_bt t1, unwrap_bt t2 with
      | S.TUnion (_, u1, u2), t -> c'' (S.TUnion (n, c' (S.TInter (None, u1, t)), c' (S.TInter (None, u2, t))))
      | t, S.TUnion (_, u1, u2) -> c'' (S.TUnion (n, c' (S.TInter (None, t, u1)), c' (S.TInter (None, t, u2))))
      | t1, t2 -> match S.canonical_type t1, S.canonical_type t2 with
        | S.TTop, t
        | t, S.TTop -> begin match t with
          | S.TEmbed t -> unwrap_t t
          | t -> embed_t t
        end
        | S.TBot, _
        | _, S.TBot -> embed_t S.TBot
        | S.TPrim p1, S.TPrim p2 -> if p1 = p2 then embed_t t1 else embed_t S.TBot (* Prims are unique *)
        | S.TEmbed (TForall(_, alpha, bound1, typ1) as t1), 
          S.TEmbed (TForall(_, beta, bound2, typ2) as t2) ->
          if equivalent_sigma IdMap.empty bound1 bound2
          then TForall(n, alpha, bound1, 
                       canonical_type
                         (embed_t (S.TInter (None, extract_t typ1, 
                                             extract_t
                                               (typ_typ_subst beta (embed_t (S.TId alpha)) typ2)))))
          else embed_t (S.TInter(n, extract_t t1, extract_t t2))
        | t1, t2 -> if t1 = t2 then embed_t t1 else embed_t (S.TInter(n, t1, t2))
    end
    | TStrobe t -> begin match S.canonical_type t with
      | S.TEmbed t -> t
      | t -> embed_t t
    end
    | TForall (n, alpha, bound, typ) -> TForall(n, alpha, canonical_sigma bound, c typ)
    | TDom(n, TDom(_, t, sel1), sel2) -> c (TDom(n, t, Css.intersect sel1 sel2))
    | TDom(n, t, sel) -> TDom(n, c t, sel)

  and canonical_multiplicity m =
    let c = canonical_multiplicity in
    (* Invariant: will never return MPlain or MId, and
     * if there are no MIds then it will never return MSum *)
    match m with
    | MPlain t -> MOne (MPlain (canonical_type t))
    | MId _ -> MOne m
    | MZero _ -> MZero (MPlain (embed_t Strobe.TBot))
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
    | MSum(m1, m2) -> 
      let c_u t1 t2 = canonical_type (embed_t (Strobe.TUnion(None, extract_t t1, extract_t t2))) in
      match c m1, c m2 with
      | MZero _, t2 -> t2
      | t1, MZero _ -> t1
      | MOne (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MOne (MPlain t1), MZeroOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MOne (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MOne (MPlain t1), MZeroPlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroOne (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroOne (MPlain t1), MZeroOne (MPlain t2) -> MZeroPlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroOne (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroOne (MPlain t1), MZeroPlus (MPlain t2) -> MZeroPlus (MPlain (canonical_type (c_u t1 t2)))
      | MOnePlus (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MOnePlus (MPlain t1), MZeroOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MOnePlus (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MOnePlus (MPlain t1), MZeroPlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroPlus (MPlain t1), MOne (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroPlus (MPlain t1), MZeroOne (MPlain t2) -> MZeroPlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroPlus (MPlain t1), MOnePlus (MPlain t2) -> MOnePlus (MPlain (canonical_type (c_u t1 t2)))
      | MZeroPlus (MPlain t1), MZeroPlus (MPlain t2) -> MZeroPlus (MPlain (canonical_type (c_u t1 t2)))
      | MPlain _, _
      | MId _, _
      | _, MPlain _
      | _, MId _ -> failwith "impossible"
      | t1, t2 -> MSum (t1, t2)


  (* exception Typ_error of Pos.t * string *)
  (* let typ_mismatch p s =  *)
  (*   if !error_on_mismatch then *)
  (*     raise (Typ_error (p, s)) *)
  (*   else begin *)
  (*     incr num_typ_errors; *)
  (*     eprintf "type error at %s : %s\n" (Pos.toString p) s *)
  (*   end *)
end

module MakeModule
  (Strobe : STROBE_MODULE)
  (Css : Css.CSS)
  (JQ : JQUERY_ACTIONS
   with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env
  with type sel = Css.t)
    : (JQUERY_MODULE
   with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type multiplicity = JQ.multiplicity
  with type sigma = JQ.sigma
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env
  with type sel = JQ.sel
  with module Strobe = Strobe
    with module Css = Css) =
struct
  include JQ
  module Strobe = Strobe
  module Css = Css
end

(* module MakeJQueryTypSub *)
(*   (Strobe : STROBE_TYPS) *)
(*   (JQuery : JQUERY_TYPS *)
(*    with type baseTyp = Strobe.typ *)
(*    with type typ = Strobe.extTyp *)
(*    with type baseKind = Strobe.kind *)
(*    with type kind = Strobe.extKind) *)
(*   (StrobeSub : TYP_SUB with type typ = Strobe.typ with type kind = Strobe.kind) *)
(*   : (TYP_SUB with type typ = JQuery.typ with type kind = JQuery.kind) = *)
(* struct *)
(*   type typ = JQuery.typ *)
(*   type kind = JQuery.kind *)
(*   let subtype t1 t2 = match t1, t2 with *)
(*     | JQuery.TStrobe t1, JQuery.TStrobe t2 -> StrobeSub.subtype t1 t2 *)
(*     | JQuery.TStrobe _, _ *)
(*     | _, JQuery.TStrobe _ -> false *)
(*     | _, _ -> t1 = t2 *)
(* end *)
