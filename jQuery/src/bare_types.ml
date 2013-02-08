open Prelude
open Sig

open Bare_sigs
open Strobe_sigs

module Make : BARE_TYP = functor (STROBE : TYPS) ->
  struct
    type baseKind = STROBE.kind
    type kind =
      (* and anything new... *)
      | KStrobe of baseKind

    type baseTyp = STROBE.typ
    type typ =
      (* and anything new... *)
      | TStrobe of baseTyp

    type baseBinding = STROBE.binding
    type binding =
      (* and anything new... *)
      | BStrobe of baseBinding

    type env = binding list IdMap.t
end

module MakeActions
  (Strobe : STROBE_ACTIONS)
  (Bare : BARE_TYPS
   with type baseTyp = Strobe.typ
   with type baseKind = Strobe.kind
   with type baseBinding = Strobe.binding
   with type typ = Strobe.extTyp
   with type kind = Strobe.extKind
   with type binding = Strobe.extBinding
   with type env = Strobe.env)
  : (BARE_ACTIONS 
   with type typ = Bare.typ
   with type kind = Bare.kind
   with type binding = Bare.binding
   with type baseTyp = Bare.baseTyp
   with type baseKind = Bare.baseKind
   with type baseBinding = Bare.baseBinding
   with type env = Bare.env) =
struct

  include Bare
  open Bare
  
  let rec embed_t t =
    match t with
      | Strobe.TEmbed (TStrobe t) -> embed_t t
      (* Matching your extended types would go here *)
      (* | Strobe.TEmbed t -> t *)
      | t -> TStrobe t
  (* Ditto extended kinds/bindings for embed_k and embed_b *)
  let rec embed_k k =
    match k with Strobe.KEmbed (KStrobe k) -> embed_k k | k -> KStrobe k
  let rec embed_b b =
    match b with Strobe.BEmbed (BStrobe b) -> embed_b b | b -> BStrobe b
  let rec extract_t t =
    match t with
      | TStrobe (Strobe.TEmbed t) -> extract_t t 
      | TStrobe t -> t 
      (* Matching your extended types would go here *)
      (* | t -> Strobe.TEmbed t *)
  (* Ditto extended kinds/bindings for extract_k and extract_b *)
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

  let expose_twith env t =
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
    and squash_t t = embed_t (squash_s (extract_t t))
    in squash_t t

  let assoc_merge = IdMap.merge (fun x opt_s opt_t -> match opt_s, opt_t with
    | Some (BStrobe (Strobe.BTermTyp (Strobe.TId y))), 
      Some (BStrobe (Strobe.BTermTyp (Strobe.TId z))) ->
      if x = y then opt_t else opt_s
    | Some t, _
    | _, Some t ->
      Some t
    | None, None -> None)
    
  let typ_assoc env t1 t2 : binding IdMap.t =
    let add_strobe x t m = 
      IdMap.add x (embed_b (Strobe.BTermTyp t)) m in
    match t1, t2 with
    | TStrobe s, TStrobe t -> 
      Strobe.typ_assoc add_strobe assoc_merge env s t

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

    let typ t = match t with
      | TStrobe t ->
        (if shouldUseNames ()
         then squish
         else label_angles "STROBE" cut) [Strobe.Pretty.typ t]

    let env e = [empty]

    let rec simpl_typ typ = match typ with
      | TStrobe t -> "TSTROBE(" ^ (Strobe.Pretty.simpl_typ t) ^ ")"

    and simpl_kind k = FormatExt.to_string kind k

  end
  let string_of_typ = FormatExt.to_string Pretty.typ
  let string_of_kind = FormatExt.to_string Pretty.kind

  let apply_name n typ = match typ with
    | TStrobe t -> embed_t (Strobe.apply_name n t)
  let name_of typ =  match typ with
    | TStrobe t -> Strobe.name_of t
  let replace_name n typ = match typ with
    | TStrobe t -> embed_t (Strobe.replace_name n t)

  (* substitute x FOR s IN t *)
  let rec typ_subst x s t = match t with
    | TStrobe tstrobe -> begin
      let typ_help = typ_subst x s in
      let subst_t =
        embed_t (Strobe.subst (Some x) (extract_t s) typ_help tstrobe)
      in unwrap_t subst_t
    end

  let free_ids typ = match typ with
    | TStrobe t -> Strobe.free_typ_ids t

  let rec equivalent_typ env t1 t2 = match t1, t2 with
    | TStrobe (Strobe.TEmbed t1), _ -> equivalent_typ env t1 t2
    | _, TStrobe (Strobe.TEmbed t2) -> equivalent_typ env t1 t2
    | TStrobe t1, TStrobe t2 -> Strobe.equivalent_typ env t1 t2
    (* This is redundant in this bare example, but you may want it *)
    (* | _ -> false *)

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

  let canonical_type typ = match typ with
    | TStrobe t -> begin match Strobe.canonical_type t with
      | Strobe.TEmbed t -> t
      | t -> embed_t t
    end

  (* if you have special-purpose type constructors that would
     be nice to un-expand, try to politely do so here, otherwise
     don't bother, and just be the identity function *)
  let collapse_if_possible env typ = typ

end

module MakeModule
  (Strobe : STROBE_MODULE)
  (Bare : BARE_ACTIONS
   with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env)
    : (BARE_MODULE
   with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env
  with module Strobe = Strobe) =
struct
  include Bare
  module Strobe = Strobe
end

