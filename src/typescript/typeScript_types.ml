open Prelude
open Sig

open TypeScript_sigs
open Strobe_sigs

module Make : TYPESCRIPT_TYP = functor (STROBE : TYPS) ->
  struct
    type baseKind = STROBE.kind
    type kind =
      (* and anything new... *)
      | KStrobe of baseKind

    type baseTyp = STROBE.typ
    type typ =
      | TStrobe of baseTyp
      | TArrow of typ list * typ option * typ

    type baseBinding = STROBE.binding
    type binding =
      (* and anything new... *)
      | BStrobe of baseBinding

    type env = binding list IdMap.t
end

module MakeActions
  (Strobe : STROBE_ACTIONS)
  (TypeScript : TYPESCRIPT_TYPS
   with type baseTyp = Strobe.typ
   with type baseKind = Strobe.kind
   with type baseBinding = Strobe.binding
   with type typ = Strobe.extTyp
   with type kind = Strobe.extKind
   with type binding = Strobe.extBinding
   with type env = Strobe.env)
  : (TYPESCRIPT_ACTIONS 
   with type typ = TypeScript.typ
   with type kind = TypeScript.kind
   with type binding = TypeScript.binding
   with type baseTyp = TypeScript.baseTyp
   with type baseKind = TypeScript.baseKind
   with type baseBinding = TypeScript.baseBinding
   with type env = TypeScript.env) =
struct

  include TypeScript
  open TypeScript
  
  let rec embed_t t =
    match t with
      | Strobe.TEmbed (TStrobe t) -> embed_t t
      | Strobe.TEmbed t -> t
      | t -> TStrobe t
  let rec embed_k k =
    match k with Strobe.KEmbed (KStrobe k) -> embed_k k | k -> KStrobe k
  let rec embed_b b =
    match b with Strobe.BEmbed (BStrobe b) -> embed_b b | b -> BStrobe b
  let rec extract_t t =
    match t with
      | TStrobe (Strobe.TEmbed t) -> extract_t t 
      | TStrobe t -> t 
      | t -> Strobe.TEmbed t
  let rec extract_k k =
    match k with KStrobe (Strobe.KEmbed k) -> extract_k k | KStrobe k -> k
  let rec extract_b b =
    match b with BStrobe (Strobe.BEmbed b) -> extract_b b | BStrobe b -> b
  let rec unwrap_bt t =
    match t with Strobe.TEmbed (TStrobe t) -> unwrap_bt t | _ -> t
  let rec unwrap_bk k =
    match k with Strobe.KEmbed (KStrobe k) -> unwrap_bk k | _ -> k
  let rec unwrap_bb b =
    match b with Strobe.BEmbed (BStrobe b) -> unwrap_bb b | _ -> b
  let rec unwrap_t t =
    match t with 
    | TStrobe (Strobe.TEmbed t) -> unwrap_t t 
    | TStrobe (Strobe.TUninit inner) -> begin
      match !inner with
      | None -> t
      | Some t' -> embed_t t'
    end
    | _ -> t
  let rec unwrap_k k =
    match k with KStrobe (Strobe.KEmbed k) -> unwrap_k k | _ -> k
  let rec unwrap_b b =
    match b with BStrobe (Strobe.BEmbed b) -> unwrap_b b | _ -> b

  let rec simpl_typ env typ =
    match typ with
    | TStrobe t -> embed_t (Strobe.simpl_typ env (extract_t typ))
    | _ -> typ

  let mapopt f t = match t with None -> None | Some t -> Some (f t)
  let expose_twith env t =
    let rec squash_s t =
      let open Strobe in
      match t with
      | TWith _ -> Strobe.simpl_typ env t
      | TRef (n, t) -> TRef (n, squash_s t)
      | TSource (n, t) -> TSource (n, squash_s t)
      | TSink (n, t) -> TSink (n, squash_s t)
      | TUnion (n, t1, t2) -> TUnion(n, squash_s t1, squash_s t2)
      | TInter(n, t1, t2) -> TInter(n, squash_s t1, squash_s t2)
      | TArrow(args, vararg, ret) -> TArrow(map squash_s args, mapopt squash_s vararg, squash_s ret)
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
      | TUninit ty -> ty := mapopt squash_s !ty; t
      | TEmbed t -> extract_t (squash_t t)
    and squash_t t = match t with
      | TStrobe t -> embed_t (squash_s t)
      | TArrow(args, vararg, ret) -> TArrow(map squash_t args, mapopt squash_t vararg, squash_t ret)
    in squash_t t

  let assoc_merge = IdMap.merge (fun x opt_s opt_t -> match opt_s, opt_t with
    | Some (BStrobe (Strobe.BTermTyp (Strobe.TId y))), 
      Some (BStrobe (Strobe.BTermTyp (Strobe.TId z))) ->
      if x = y then opt_t else opt_s
    | Some t, _
    | _, Some t ->
      Some t
    | None, None -> None)
    
  let rec typ_assoc env t1 t2 = typ_assoc' env t1 t2
    (* trace "TypeScript:typ_assoc" *)
    (* (Pretty.simpl_typ t1 ^ " with " ^ Pretty.simpl_typ t2) *)
    (* (fun _ -> true) (fun () -> (typ_assoc' add merge env t1 t2)) *)
  and typ_assoc' (env : env) (t1 : typ) (t2 : typ) =
    let add_strobe x t m = 
      IdMap.add x (embed_b (Strobe.BTermTyp t)) m in
    match t1, t2 with
    | TStrobe s, TStrobe t -> 
      Strobe.typ_assoc add_strobe assoc_merge env s t
    | TArrow (args1, v1, r1), TArrow (args2, v2, r2) ->
      List.fold_left assoc_merge
        ((fun base -> match v1, v2 with
        | Some v1, Some v2 -> assoc_merge (typ_assoc env v1 v2) base
        | _ -> base)
            (typ_assoc env r1 r2))
        (ListExt.map2_noerr (typ_assoc env) args1 args2)
    | _ -> IdMap.empty

  module Pretty = struct
    open Format
    open FormatExt

    let useNames, shouldUseNames =
      let _useNames = ref true in
      let useNames b = _useNames := b; Strobe.Pretty.useNames b in
      let shouldUseNames () = !_useNames in
      useNames, shouldUseNames

    let kind k = match k with
      | KStrobe k ->
        (if shouldUseNames ()
         then squish
         else label_angles "KSTROBE" cut) [Strobe.Pretty.kind k]

    let rec typ t = typ' false t
    and typ' horzOnly t =
      let typ = typ' horzOnly in 
      let hnestOrHorz n = if horzOnly then horz else (fun ps -> hnest n (squish ps)) in
      match t with
      | TStrobe t ->
        (if shouldUseNames ()
         then squish
         else label_angles "STROBE" cut) [Strobe.Pretty.typ t]
      | TArrow (tt::arg_typs, varargs, r_typ) ->
        let multiLine = horzOnly ||
          List.exists (fun at -> match extract_t at with 
            Strobe.TEmbed (TArrow _) | Strobe.TObject _ -> true | _ -> false) arg_typs in
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

    let env e = [empty]

    let rec simpl_typ typ = match typ with
      | TStrobe t -> "TSTROBE(" ^ (Strobe.Pretty.simpl_typ t) ^ ")"
      | TArrow _ -> "_ -> _"

    and simpl_kind k = FormatExt.to_string kind k

  end
  let string_of_typ = FormatExt.to_string Pretty.typ
  let string_of_kind = FormatExt.to_string Pretty.kind

  let apply_name n typ = match typ with
    | TStrobe t -> embed_t (Strobe.apply_name n t)
    | TArrow _ -> typ
  let name_of typ =  match typ with
    | TStrobe t -> Strobe.name_of t
    | TArrow _ -> None
  let replace_name n typ = match typ with
    | TStrobe t -> embed_t (Strobe.replace_name n t)
    | TArrow _ -> typ

  (* substitute x FOR s IN t *)
  let rec typ_subst x s t = 
    let typ_help = typ_subst x s in
    match t with
    | TStrobe tstrobe -> begin
      let subst_t =
        embed_t (Strobe.subst (Some x) (extract_t s) typ_help tstrobe)
      in unwrap_t subst_t
    end
    | TArrow(args, varargs, ret) -> TArrow(map typ_help args, mapopt typ_help varargs, typ_help ret)

  let rec free_ids typ =
    let open IdSet in
    let open IdSetExt in
    match typ with
    | TStrobe t -> Strobe.free_ids t
    | TArrow (ss, v, t) ->
      unions (free_ids t :: (match v with None -> empty | Some v -> free_ids v) :: (map free_ids ss))


  let rec equivalent_typ env t1 t2 = match t1, t2 with
    | TStrobe (Strobe.TEmbed t1), _ -> equivalent_typ env t1 t2
    | _, TStrobe (Strobe.TEmbed t2) -> equivalent_typ env t1 t2
    | TStrobe t1, TStrobe t2 -> Strobe.equivalent_typ env t1 t2
    | TArrow (args1, v1, r1), TArrow (args2, v2, r2) ->
      List.length args1 = List.length args2
      && List.for_all2 (equivalent_typ env) args1 args2
      && equivalent_typ env r1 r2
      && (match v1, v2 with
      | None, None -> true
      | Some v1, Some v2 -> equivalent_typ env v1 v2
      | _ -> false)
    | _ -> false

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
          (x::new_ys, IdMap.add y (embed_t (Strobe.TId x)) substs))
        ([], IdMap.empty) ys in
    let new_ys = List.rev rev_new_ys in
    let t' = IdMap.fold typ_subst substs t in
    (new_ys, t')

  let rec canonical_type typ = 
    let c = canonical_type in
    let c'' t = c (embed_t t) in
    let c' t = extract_t (c'' t) in
    match unwrap_t typ with
    | TStrobe(Strobe.TUnion (n, _, _)) -> begin
      let rec collect t = match unwrap_t t with
        | TStrobe(Strobe.TUnion (_, t1, t2)) -> collect (c (embed_t t1)) @ collect (c (embed_t t2))
        | TStrobe(Strobe.TEmbed t) -> failwith "impossible: embed_t should've removed this case"
        | TStrobe t -> [unwrap_bt t]
        | _ -> [extract_t t] in
      let pieces = collect typ in
      let nodups = ListExt.remove_dups pieces in
      match List.rev nodups with
      | [] -> failwith "impossible, 008"
      | hd::tl -> 
        embed_t (Strobe.apply_name n (List.fold_left (fun acc t ->
                     if t = Strobe.TBot
                     then acc 
                     else Strobe.TUnion(None, t, acc)) hd tl))
    end
    | TStrobe(Strobe.TInter (n, t1, t2)) -> begin
      match unwrap_bt t1, unwrap_bt t2 with
      | Strobe.TUnion (_, u1, u2), t -> c'' (Strobe.TUnion (n, c' (Strobe.TInter (None, u1, t)), c' (Strobe.TInter (None, u2, t))))
      | t, Strobe.TUnion (_, u1, u2) -> c'' (Strobe.TUnion (n, c' (Strobe.TInter (None, t, u1)), c' (Strobe.TInter (None, t, u2))))
      | t1, t2 -> match Strobe.canonical_type t1, Strobe.canonical_type t2 with
        | Strobe.TTop, t
        | t, Strobe.TTop -> begin match t with
          | Strobe.TEmbed t -> unwrap_t t
          | t -> embed_t t
        end
        | Strobe.TBot, _
        | _, Strobe.TBot -> embed_t Strobe.TBot
        | Strobe.TPrim p1, Strobe.TPrim p2 -> if p1 = p2 then embed_t t1 else embed_t Strobe.TBot (* Prims are unique *)
        | t1, t2 -> if t1 = t2 then embed_t t1 else embed_t (Strobe.TInter(n, t1, t2))
    end
    | TStrobe t -> begin 
      match Strobe.canonical_type t with
      | Strobe.TEmbed t -> t
      | t -> embed_t t
    end
    | TArrow (args, var, ret) -> TArrow (map c args, mapopt c var, c ret)

  (* if you have special-purpose type constructors that would
     be nice to un-expand, try to politely do so here, otherwise
     don't bother, and just be the identity function *)
  let collapse_if_possible env typ = typ

end

module MakeModule
  (Strobe : STROBE_MODULE)
  (TypeScript : TYPESCRIPT_ACTIONS
   with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env)
    : (TYPESCRIPT_MODULE
   with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env
  with module Strobe = Strobe) =
struct
  include TypeScript
  module Strobe = Strobe
end

