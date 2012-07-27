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
    | TLambda of string option * (id * kind) list * typ (** type operator *)
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
  (Pat : SET with type t = Strobe.pat)
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


  let rec wf_jtyp (t : typ) : bool = match (unwrap_t t) with
    | TForall (_, id, s, t) -> wf_sigma s && wf_jtyp t
    | TLambda (_, _, t) -> wf_jtyp t
    | TApp (t, sl) -> wf_jtyp t && List.for_all wf_sigma sl
    | TDom (_, t, _) -> wf_jtyp t
    | TStrobe b -> wf_bt b
  and wf_mult (m : multiplicity) : bool = match m with
    | MPlain t -> wf_jtyp t
    | MId _ -> true
    | MZero m
    | MOne m
    | MZeroOne m
    | MOnePlus m
    | MZeroPlus m -> wf_mult m
    | MSum (m1, m2) -> wf_mult m1 && wf_mult m2
  and wf_sigma (s : sigma) : bool = match s with
    | STyp t -> wf_jtyp t
    | SMult m -> wf_mult m
  and wf_bt (b : baseTyp) : bool = match (unwrap_bt b) with
    | Strobe.TPrim _ -> true
    | Strobe.TUnion (_, b1, b2)
    | Strobe.TInter (_, b1, b2) -> wf_bt b1 && wf_bt b2
    | Strobe.TArrow (bl, None, b) -> List.for_all wf_bt bl && wf_bt b
    | Strobe.TArrow (bl, Some bopt, b) -> List.for_all wf_bt bl && wf_bt bopt && wf_bt b
    | Strobe.TThis bt -> wf_bt bt
    | Strobe.TObject objt -> wf_obj_typ objt
    | Strobe.TWith (bt, objt) -> wf_bt bt && wf_obj_typ objt
    | Strobe.TRegex _ -> true
    | Strobe.TRef (_, bt)
    | Strobe.TSource (_, bt)
    | Strobe.TSink (_, bt) -> wf_bt bt
    | Strobe.TTop
    | Strobe.TBot -> true
    | Strobe.TForall (_, _, bt1, bt2) -> wf_bt bt1 && wf_bt bt2
    | Strobe.TId _ -> true
    | Strobe.TRec (_, _, bt) -> wf_bt bt
    | Strobe.TLambda (_, _, bt) -> wf_bt bt
    | Strobe.TApp (bt, bts) -> wf_bt bt && List.for_all wf_bt bts
    | Strobe.TFix (_, _, _, bt) -> wf_bt bt
    | Strobe.TUninit r -> (match !r with None -> true | Some bt -> wf_bt bt)
    | Strobe.TEmbed _ -> false
  and wf_obj_typ (objt : Strobe.obj_typ) : bool = 
    let typs = List.map thd3 (Strobe.fields objt) in
    List.for_all wf_bt typs
    

  let well_formed = wf_jtyp

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
    | TLambda(None, ts, t) -> TLambda(n, ts, t)
    | TDom(None, t, sel) -> TDom(n, t, sel)
    | _ -> typ

  and name_of typ =  match typ with
    | TStrobe t -> Strobe.name_of t
    | TForall(name, _, _, _) -> name
    | TLambda(name, _, _) -> name
    | TDom(name, _, _) -> name
    | _ -> None

  and replace_name n typ = match typ with
    | TStrobe t -> embed_t (Strobe.replace_name n t)
    | TForall(_, x, t, b) -> TForall(n, x, t, b)
    | TLambda(_, ts, t) -> TLambda(n, ts, t)
    | TDom(_, t, sel) -> TDom(n, t, sel)
    | _ -> typ


  (* pretty printing *)
  module Pretty = struct
    open Format
    open FormatExt

    let useNames, shouldUseNames =
      let _useNames = ref true in
      let useNames b = _useNames := b; Strobe.Pretty.useNames b in
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
        namedType name (horzOrVert [horz [text "JQForall"; binding; text "."];
                                    typ body])
      end
      | TLambda (n, args, t) -> 
        let p (x, k) = horz [ text x; text "::"; kind k ] in
        namedType n (hvert [horz [text "JQLambda"; horz (map p args); text "."]; typ t ])
      | TApp (t, ts) ->
        (match ts with
        | [] -> horz [typ t; text "<>"]
        | _ -> parens
          [squish [typ t; 
                   angles (add_sep_between (text ",") (map sigma ts))]])
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

    let rec simpl_typ typ = match typ with
      | TStrobe t -> "TSTROBE(" ^ (Strobe.Pretty.simpl_typ t) ^ ")"
      | TDom(name, _, sel) -> 
        let desc = match name with Some n -> n | None -> FormatExt.to_string Css.p_css sel in
        "JQ.TDom " ^ desc
      | TForall(name, a, _, _) ->
        let desc = match name with Some n -> n | None -> a ^ "<:**.***" in
        "JQ.TForall " ^ desc
      | TLambda(name, yks, _) ->
        let desc = match name with Some n -> n | None -> "(" ^ (String.concat "," (map fst2 yks)) ^ ")" in
        "JQ.TLambda " ^ desc
      | TApp(t, ts) -> Printf.sprintf "JQ.%s<%s>" (simpl_typ t) (String.concat "," (map simpl_sigma ts))
    and simpl_mult mult = match mult with
      | MPlain t -> simpl_typ t
      | MId x -> "`" ^ x
      | MOne m -> "1<" ^ (simpl_mult m) ^ ">"
      | MZero m -> "0<" ^ (simpl_mult m) ^ ">"
      | MZeroOne m -> "01<" ^ (simpl_mult m) ^ ">"
      | MOnePlus m -> "1+<" ^ (simpl_mult m) ^ ">"
      | MZeroPlus m -> "0+<" ^ (simpl_mult m) ^ ">"
      | MSum (m1, m2) -> "Sum<" ^ (simpl_mult m1) ^ "++" ^ (simpl_mult m2) ^ ">"
    and simpl_sigma sigma = match sigma with
      | STyp t -> simpl_typ t
      | SMult m -> simpl_mult m
    and simpl_kind k = FormatExt.to_string kind k
  end
  let string_of_typ = FormatExt.to_string Pretty.typ
  let string_of_mult = FormatExt.to_string Pretty.multiplicity
  let string_of_kind = FormatExt.to_string Pretty.kind
  let string_of_sigma s = match s with STyp t -> string_of_typ t | SMult m -> string_of_mult m

  (* free type variables *)
  (* let rec free_sigma_ids s =  *)
  (*   let rec free_typ_ids t = *)
  (*   let open IdSet in *)
  (*   let open IdSetExt in *)
  (*   match t with *)
  (*   | TStrobe t -> Strobe.free_typ_ids t *)
  (*   | TLambda (_, xks, t) -> *)
  (*     let (ts, ms) = (free_typ_ids t) in *)
  (*     let (xts, yms) = List.partition (fun (_, k) -> match k with KMult _ -> true | _ -> false) xks in *)
  (*     let (xs, ys) = (from_list (map fst2 xts), from_list (map fst2 yms)) in *)
  (*     (diff ts xs, diff ms ys) *)
  (*   | TApp (t, ss) -> map_pair unions (List.split (free_typ_ids t :: (map free_sigma_ids ss))) *)
  (*   | TForall (_, alpha, bound, typ) -> *)
  (*     let (f1t, f1m) = (free_sigma_ids bound) in *)
  (*     let (f2t, f2m) = (free_typ_ids typ) in *)
  (*     (match bound with *)
  (*     | STyp _ -> (remove alpha (union f1t f2t), union f1m f2m) *)
  (*     | SMult _ -> (union f1t f2t, remove alpha (union f1m f2m))) *)
  (*   | TDom(_, t, _) -> free_typ_ids t *)
  (*   and free_mult_ids m = *)
  (*     let open IdSet in *)
  (*     let open IdSetExt in *)
  (*     match m with *)
  (*     | MPlain t -> free_typ_ids t *)
  (*     | MId name -> (empty, singleton name) *)
  (*     | MZero m *)
  (*     | MOne m *)
  (*     | MZeroOne m *)
  (*     | MOnePlus m *)
  (*     | MZeroPlus m -> free_mult_ids m *)
  (*     | MSum(m1, m2) -> *)
  (*       let (f1t, f1m) = (free_mult_ids m1) in *)
  (*       let (f2t, f2m) = (free_mult_ids m2) in *)
  (*       (union f1t f2t, union f1m f2m) *)
  (*   in match s with *)
  (*   | STyp t -> free_typ_ids t *)
  (*   | SMult m -> free_mult_ids m *)




  let rec free_typ_ids t = match t with
    | TDom(_, t, _) -> free_typ_ids t
    | TForall (_, alpha, bound, typ) ->
      let free_t = match bound with
        | STyp _ -> IdSet.remove alpha (free_typ_ids typ)
        | SMult _ -> free_typ_ids typ in
      IdSet.union (free_sigma_typ_ids bound) free_t
    | TLambda (_, yks, t) ->
      IdSet.diff (free_typ_ids t) (IdSetExt.from_list (List.map fst2 yks))
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
      let free_t = match bound with
        | STyp _ -> IdSet.remove alpha (free_typ_ids typ)
        | SMult _ -> free_typ_ids typ in
      IdSet.union (free_sigma_mult_ids bound) free_t
    | TLambda (_, yks, t) ->
      IdSet.diff (free_typ_ids t) (IdSetExt.from_list (List.map fst2 yks))
    | TApp (t, ss) -> IdSetExt.unions (free_typ_ids t :: (map free_sigma_typ_ids ss))
    | TStrobe t -> 
      let ret = Strobe.map_reduce_t 
        free_typ_mult_ids (* map over extTyps *)
        (fun bound id -> if IdSet.mem id bound then IdSet.empty else IdSet.singleton id) (* TIds, ignoring bound *)
        (fun bound ids1 ids2 -> IdSet.diff (IdSet.union ids1 ids2) bound) (* combine, ignoring bound vars *)
        IdSet.empty t in
      (* Strobe.traceMsg "Free_typ_mult_ids for %s are %s" (string_of_typ (TStrobe t))  *)
      (*   (String.concat "," (IdSetExt.to_list ret)); *)
      ret
  and free_sigma_mult_ids s = match s with
    | STyp t -> free_typ_ids t
    | SMult m -> free_mult_typ_ids m
      
  let free_ids t = IdSet.union (free_typ_ids t) (free_typ_mult_ids t)

  let free_sigma_ids s = (free_sigma_typ_ids s, free_sigma_mult_ids s)


  let rec extract_mult m = match m with
    | MPlain t -> ((STyp t), fun s -> begin 
      match s with
      | STyp t -> MPlain t
      | SMult m -> m
    end)
    | MOne m ->
      let (s, m) = extract_mult m in
      (s, fun s -> MOne (m s))
    | MZero m ->
      let (s, m) = extract_mult m in
      (s, fun s -> MZero (m s))
    | MOnePlus m ->
      let (s, m) = extract_mult m in
      (s, fun s -> MOnePlus (m s))
    | MZeroOne m ->
      let (s, m) = extract_mult m in
      (s, fun s -> MZeroOne (m s))
    | MZeroPlus m ->
      let (s, m) = extract_mult m in
      (s, fun s -> MZeroPlus (m s))
    | MId _
    | MSum _ ->
      ((SMult m), fun s -> begin match s with
      | STyp _ -> failwith "expected multiplicity, got typ"
      | SMult m -> m
      end)
  (* failwith ("can't handle MId(" ^ m ^ ") here") *)
  (* failwith "can't handle MSums here" *)

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
    let t'' = match t' with STyp t -> t | _ -> failwith "Rename_avoid_capture impossible" in
    (new_ys, t'')

  and subst x (s : sigma) (sigma : sigma) : sigma =
    let rec sigma_help sigma : sigma = match sigma with
      | STyp typ -> typ_sigma_help typ
      | SMult mult -> SMult (mult_help mult)
    and mult_help mult = mult_help' mult
      (* Strobe.trace "JQsubst_mult_help"  *)
      (*   (Pretty.simpl_sigma sigma ^ "[" ^ Pretty.simpl_mult mult ^ "/" ^ x ^ "]")  *)
      (*   (fun _ -> true) (fun () -> mult_help' mult) *)
    and mult_help' mult : multiplicity = match mult with
      | MPlain typ -> typ_mult_help typ
      | MId y -> if x = y then begin
        (match s with 
        | SMult m -> m
        | STyp t -> mult)
      end else mult
      | MZero m -> MZero (mult_help m)
      | MOne m -> MOne (mult_help m)
      | MZeroOne m -> MZeroOne (mult_help m)
      | MOnePlus m -> MOnePlus (mult_help m)
      | MZeroPlus m -> MZeroPlus (mult_help m)
      | MSum (m1, m2) -> MSum (mult_help m1, mult_help m2)
    and typ_sigma_help typ : sigma = match typ with
      | TStrobe (Strobe.TId y) -> 
        if y = x then s else STyp typ
      | _ -> STyp (typ_help typ)
    and typ_mult_help typ : multiplicity = match typ_sigma_help typ with
      | STyp t -> MPlain t
      | SMult m -> m
    and typ_help typ = typ_help' typ
      (* Strobe.trace "JQsubst_typ_help"  *)
      (*   (Pretty.simpl_sigma sigma ^ "[" ^ Pretty.simpl_typ typ ^ "/" ^ x ^ "]") *)
      (*   (fun _ -> true) (fun () -> typ_help' typ) *)
    and typ_help' typ : typ = match typ with
      (* | TStrobe (Strobe.TId y) -> if y = x then begin *)
      (*   match s with *)
      (*   | STyp t -> t *)
      (*   | SMult m -> *)
      (*     let msg = sprintf "ill-kinded substitution: %s[%s/%s] is not a type" *)
      (*       (string_of_typ typ) (string_of_sigma s) x in *)
      (*     raise (Invalid_argument msg) *)
      (* end else typ *)
      | TStrobe tstrobe -> begin
        let subst_t = match s with
          | STyp t -> 
            embed_t (Strobe.subst (Some x) (extract_t t) typ_help tstrobe)
          | SMult m -> embed_t (Strobe.subst None Strobe.TTop typ_help tstrobe)
        in unwrap_t subst_t
      end
      | TApp(f, args) -> 
        (* Strobe.traceMsg "Substituting %s->%s in %s" x (string_of_sigma s) (string_of_typ typ); *)
        TApp(typ_help f, List.map sigma_help args)
      | TLambda (n, yks, t) ->
        (* Strobe.traceMsg "JQTLambda %s" (string_of_typ typ); *)
        if List.exists (fun (y, _) -> y = x) yks then typ
        else
          let (ys, ks) = List.split yks in
          let (free_t, free_m) = free_sigma_ids s in
          let free = IdSet.union free_t free_m in
          let (new_ys, t') = rename_avoid_capture free ys t in
          let new_yks = List.combine new_ys ks in
          TLambda (n, new_yks, typ_help t')
      | TForall (name, alpha, bound, body) -> if x = alpha then typ else
          let (free_t, free_m) = free_sigma_typ_ids s, free_sigma_mult_ids s in
          let (beta, body') = rename_avoid_capture (IdSet.union free_t free_m) [alpha] body in
          TForall (name, (List.hd beta), sigma_help bound, typ_help body')
      | TDom (name, t, sel) -> TDom(name, typ_help t, sel)
    in sigma_help sigma

  and sig_typ_subst x s typ = match subst x s (STyp typ) with STyp t -> canonical_type t | _ -> failwith "impossible1"
  and typ_typ_subst x t typ = match subst x (STyp t) (STyp typ) with STyp t -> canonical_type t | _ -> failwith "impossible2"
  and typ_mult_subst x t m = match subst x (STyp t) (SMult m) with SMult m -> canonical_multiplicity m | _ -> failwith "impossible3"
  and sig_mult_subst x s mult = match subst x s (SMult mult) with SMult m -> canonical_multiplicity m | _ -> failwith "impossible4"
  and mult_typ_subst x m t = match subst x (SMult m) (STyp t) with STyp t -> canonical_type t | SMult m' -> (* Strobe.traceMsg "Mult_typ_subst %s[%s/%s] = %s??? failed" (string_of_typ t) (string_of_mult m) x (string_of_mult m'); *) failwith "impossible5"
  and mult_mult_subst x m mult = match subst x (SMult m) (SMult mult) with SMult m -> canonical_multiplicity m | _ -> failwith "impossible6"
  and typ_subst x t typ = typ_typ_subst x t typ


  (* simple structural equivalence -- e.g. up to permutation of parts of Union or Inter or Sum
   * and can be extended to objects later... *)
  and equivalent_sigma (env : env) s1 s2 =
    match s1, s2 with
    | STyp t1, STyp t2 -> equivalent_typ env t1 t2
    | SMult m1, SMult m2 -> equivalent_multiplicity env m1 m2
    | _ -> false
  and equivalent_typ env t1 t2 = match t1, t2 with
    | TForall(_, alpha, s1, t1), TForall(_, beta, s2, t2) ->
      equivalent_sigma env s1 s2 && (match s1 with
      | SMult _ -> equivalent_typ env t1 (mult_typ_subst beta (MId alpha) t2)
      | STyp _ -> equivalent_typ env t1 (typ_typ_subst beta (embed_t (Strobe.TId alpha)) t2))
    | TLambda(_, args1, ret1), TLambda(_, args2, ret2) ->
      if (List.length args1 <> List.length args2) then false
      else if not (List.for_all2 (fun (_, k1) (_, k2) -> k1 = k2) args1 args2) then false
      else
        let ret2 = List.fold_left2 (fun r (x1,k1) (x2,k2) ->
          match k1 with
          | KMult _ -> mult_typ_subst x2 (MId x1) r
          | _ -> typ_typ_subst x2 (embed_t (Strobe.TId x1)) r) ret2 args1 args2
        in equivalent_typ env ret1 ret2
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
  and canonical_sigma s = match s with
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
      | [] -> failwith "impossible 7"
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
    | TLambda(n, ts, t) -> TLambda(n, ts, c t)
    | TDom(n, TDom(_, t, sel1), sel2) -> c (TDom(n, t, Css.intersect sel1 sel2))
    | TDom(n, t, sel) -> TDom(n, c t, sel)

  and canonical_multiplicity m =
    let c = canonical_multiplicity in
    (* Invariant: will never return MPlain or MId, and
     * if there are no MIds then it will never return MSum *)
    match m with
    | MPlain t -> MOne (MPlain (canonical_type t))
    | MId _ -> MOne m
    | MZero m -> 
      let (s, f) = extract_mult (c m) in
      begin match s with
      | STyp t -> MZero (MPlain t)
      | SMult m -> MZero m
      end
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
      | _, MId _ -> failwith "impossible 8"
      | t1, t2 -> MSum (t1, t2)

  let rec simpl_typ env typ =
    match typ with
    | TStrobe t -> embed_t (Strobe.simpl_typ env (extract_t typ))
    | TApp (t, ts) -> begin
      match embed_t (Strobe.expose env (extract_t (simpl_typ env t))) with
      | TLambda (n, args, u) -> 
        let name = match n with
          | None -> None
          | Some n ->
            let names = intersperse ", "
              (List.map (fun s -> match s with
              | SMult m -> string_of_mult m 
              | STyp t -> match name_of t with Some n -> n | None -> string_of_typ t) ts) in
            Some (n ^ "<" ^ (List.fold_right (^) names ">")) in
        apply_name name
          (simpl_typ env
             (List.fold_right2 (* well-kinded, no need to check *)
                (fun (x, k) t2 u -> sig_typ_subst x t2 u)
                args ts u))
      | func_t ->
        let msg = sprintf "ill-kinded type application in JQ.simpl_typ. Type is \
                           \n%s\ntype in function position is\n%s\n"
          (string_of_typ typ) (string_of_typ func_t) in
        raise (Invalid_argument msg)
    end
    | _ -> typ



  let squash env t = 
    let rec optsquash t = match t with None -> None | Some t -> Some (squash_s t)
    and squash_s t =
      let open Strobe in
      match t with
      | TWith _ -> Strobe.simpl_typ env t
      | TRef (n, t) -> TRef (n, squash_s t)
      | TSource (n, t) -> TSource (n, squash_s t)
      | TSink (n, t) -> TSink (n, squash_s t)
      | TUnion (n, t1, t2) -> TUnion(n, squash_s t1, squash_s t2)
      | TInter(n, t1, t2) -> TInter(n, squash_s t1, squash_s t2)
      | TArrow(args, vararg, ret) -> TArrow(map squash_s args, optsquash vararg, squash_s ret)
      | TObject ot -> TObject (mk_obj_typ (map (third3 squash_s) (fields ot)) (absent_pat ot))
      | TTop
      | TBot -> t
      | TForall(n, id, t, b) -> TForall(n, id, squash_s t, squash_s b)
      | TId _ 
      | TRegex _
      | TPrim _ -> t
      | TThis t -> TThis (squash_s t)
      | TRec(n, id, t) -> TRec(n, id, squash_s t)
      | TLambda (n, args, t) -> TLambda(n, args, squash_s t)
      | TApp(t, ts) -> TApp(squash_s t, map squash_s ts)
      | TFix(n, id, k, t) -> TFix(n, id, k, squash_s t)
      | TUninit ty -> ty := optsquash !ty; t
      | TEmbed t -> extract_t (squash_t t)
    and squash_t t =
      match t with
      | TStrobe t -> embed_t (squash_s t)
      | TLambda (n, args, t) -> TLambda(n, args, squash_t t)
      | TForall(n, id, s, t) -> TForall(n, id, squash_sig s, squash_t t)
      | TApp(t, ss) -> TApp(squash_t t, List.map squash_sig ss)
      | TDom(n, t, s) -> TDom(n, squash_t t, s)
    and squash_sig s =
      match s with
      | SMult m -> SMult (squash_m m)
      | STyp t -> STyp (squash_t t)
    and squash_m m =
      match m with
      | MPlain t -> MPlain (squash_t t)
      | MId _ -> m
      | MZero m -> MZero (squash_m m)
      | MOne m -> MOne (squash_m m)
      | MOnePlus m -> MOnePlus (squash_m m)
      | MZeroOne m -> MZeroOne (squash_m m)
      | MZeroPlus m -> MZeroPlus (squash_m m)
      | MSum (m1, m2) -> MSum (squash_m m1, squash_m m2)
    in 
    squash_t t

  let rec collapse_if_possible env typ = match unwrap_t typ with
    | TStrobe (Strobe.TSource (_, Strobe.TObject o)) -> begin
      let ofields = Strobe.fields o in
      try
        let (_, _, thisTyp) = List.find (fun (p, _, _) ->
          Pat.is_equal p (Pat.singleton "__this__")) ofields in
        begin
          match embed_t thisTyp with
          | TApp(TStrobe (Strobe.TFix(Some "jQ", _, _, _)), [SMult m; prev]) as collapsed ->
            if typ = (simpl_typ env collapsed)
            then collapsed else typ
          | _ -> typ
        end
      with Not_found -> TStrobe (Strobe.TObject o)
    end
    | t -> t


  let assoc_merge = IdMap.merge (fun x opt_s opt_t -> match opt_s, opt_t with
    | Some (BStrobe (Strobe.BTermTyp (Strobe.TId y))), 
      Some (BStrobe (Strobe.BTermTyp (Strobe.TId z)))
    | Some (BMultBound (MId y, _)), Some (BMultBound (MId z, _)) ->
      if x = y then opt_t else opt_s
    | Some (BStrobe (Strobe.BTermTyp (Strobe.TId _))), Some t
    | Some t, Some (BStrobe (Strobe.BTermTyp (Strobe.TId _)))
    | Some (BMultBound (MId _, _)), Some t
    | Some t, Some (BMultBound (MId _, _)) -> Some t
    | Some t, _
    | _, Some t ->
      Some t
    | None, None -> None)


  let rec typ_assoc env t1 t2  =
    Strobe.trace "JQtyp_assoc" 
      (string_of_typ t1 ^ " with " ^ string_of_typ t2) 
      (fun _ -> true) (fun () -> typ_assoc' env t1 t2)
  and typ_assoc' env t1 t2 : binding IdMap.t =

    let add_strobe x t m = 
      (* Strobe.traceMsg "In JQ.add_strobe %s -> %s" x (string_of_typ (embed_t t)); *)
      IdMap.add x (embed_b (Strobe.BTermTyp t)) m in

    (* consumes TApp and a source TObject and produces (m1, m2), where
       m1 is the multiplicity from ... *)
    let get_this o =
      let ofields = Strobe.fields o in
      let (_, _, thisTyp) = List.find (fun (p, _, _) ->
        Pat.is_equal p (Pat.singleton "__this__")) ofields in
      (thisTyp) in

    match t1, t2 with
    | TStrobe s, TStrobe t -> Strobe.typ_assoc add_strobe assoc_merge env s t
      (* Cases for two-arg jq *)
    | TApp (TStrobe (Strobe.TFix(Some "jQ", _, _,_)), [SMult mult; STyp prev]), 
      TStrobe (Strobe.TSource (_, Strobe.TObject o)) -> 
      Strobe.traceMsg "JQUERY_typ_assoc: associating jq with an obj";
      begin
        match embed_t (get_this o) with
        | (TApp (TStrobe (Strobe.TFix(Some "jQ", _, _,_)), 
                       [SMult this_mult; STyp this_prev])) ->
            assoc_merge 
            (mult_assoc env (canonical_multiplicity mult)
               (canonical_multiplicity this_mult))
            (typ_assoc env prev this_prev)
        | _ -> IdMap.empty
      end
    |  (TStrobe (Strobe.TSource (_, Strobe.TObject o))),
        (TApp (TStrobe (Strobe.TFix(Some "jQ", _, _,_)), [SMult mult; STyp prev])) -> 
      Strobe.traceMsg "JQuery_typ_assoc: associating an obj with a jq";
      begin
        match embed_t (get_this o) with
        | (TApp (TStrobe (Strobe.TFix(Some "jQ", _, _,_)), 
                       [SMult this_mult; STyp this_prev])) ->
            assoc_merge 
            (mult_assoc env (canonical_multiplicity this_mult)
               (canonical_multiplicity mult))
            (typ_assoc env this_prev prev)
        | _ -> IdMap.empty
      end
    | TApp (s1, s2), TApp(t1, t2) ->
      if List.length s2 <> List.length t2 then IdMap.empty else
      List.fold_left2 (fun acc t1 t2 -> 
        match t1, t2 with
        | STyp t1, STyp t2 -> assoc_merge acc (typ_assoc env t1 t2)
        | SMult t1, SMult t2 -> assoc_merge acc (mult_assoc env t1 t2)
        | _ -> IdMap.empty)
        (typ_assoc env s1 t1)
        s2 t2
    | TApp (s1, s2), t -> 
      typ_assoc env (simpl_typ env (TApp (s1, s2))) t
    | t, TApp (s1, s2) -> 
      let str_t1 = (string_of_typ t) in
      let str_t2 = (string_of_typ (TApp (s1, s2))) in
      (* Strobe.traceMsg "JQtyp_assoc %s with %s\n" str_t1 str_t2; *)
      typ_assoc env t (simpl_typ env (TApp (s1, s2)))
    | TForall (_, x, STyp s1, s2), TForall (_, y, STyp t1, t2) ->
      assoc_merge (typ_assoc env s1 t1) (typ_assoc env s2 t2)
    | TForall (_, x, SMult s1, s2), TForall (_, y, SMult t1, t2) ->
      assoc_merge (mult_assoc env s1 t1) (typ_assoc env s2 t2)
    | TDom(_, s1, _), TDom(_, s2, _) ->
      typ_assoc env s1 s2
    | _ -> IdMap.empty
  and mult_assoc env m1 m2 =
    Strobe.traceMsg "JQmult_assoc %s with %s\n" (string_of_mult m1) (string_of_mult m2);
    match m1, m2 with
    | MId m, _ -> IdMap.singleton m (BMultBound(m2, KMult (KStrobe Strobe.KStar)))
    | MPlain t1, MPlain t2 -> typ_assoc env t1 t2
    | MOne m, m2 -> mult_assoc env m m2
    | MZeroOne m1, MOne m2
    | MOnePlus m1, MOne m2
    | MZeroPlus m1, MOne m2
    | MZero m1, MZero m2
    | MZeroOne m1, MZero m2
    | MZeroPlus m1, MZero m2
    | MZeroOne m1, MZeroOne m2
    | MZeroPlus m1, MZeroOne m2
    | MOnePlus m1, MOnePlus m2
    | MZeroPlus m1, MOnePlus m2
    | MZeroPlus m1, MZeroPlus m2 -> mult_assoc env m1 m2
    | MSum(m11, m12), MSum(m21, m22) ->
      assoc_merge (mult_assoc env m11 m21) (mult_assoc env m12 m22)
    | _ -> IdMap.empty
    
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
