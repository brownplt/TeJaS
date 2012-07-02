open Prelude
open Sig
open Strobe_sigs

module L = ListExt


module MakeActions 
  (Pat : SET)
  (STROBE : STROBE_ACTIONS with type pat = Pat.t)
  (Ext : EXT_TYP_SUBTYPING with type typ = STROBE.extTyp with type kind = STROBE.extKind with type binding = STROBE.extBinding with type baseTyp = STROBE.typ with type baseKind = STROBE.kind with type baseBinding = STROBE.binding with type env = STROBE.env)
  : (STROBE_SUBTYPING with type typ = STROBE.typ with type kind = STROBE.kind with type binding = STROBE.binding with type extTyp = STROBE.extTyp with type extKind = STROBE.extKind with type extBinding = STROBE.extBinding with type pat = STROBE.pat with type obj_typ = STROBE.obj_typ with type env = STROBE.env) =
struct
  include STROBE
  open STROBE


  let num_typ_errors = ref 0

  let error_on_mismatch = ref false

  let with_typ_exns thunk = 
    let prev = !error_on_mismatch in
    error_on_mismatch := true;
    let r = thunk () in
    error_on_mismatch := prev;
    r

  let get_num_typ_errors () = !num_typ_errors

  type typ_error_details =
    | TypKind of (typ -> kind -> string) * typ * kind
    | StringTyp of (string -> typ -> string) * string * typ
    | FixedString of string
    | String of (string -> string) * string
    | TypTyp of (typ -> typ -> string) * typ * typ
    | NumNum of (int -> int -> string) * int * int
    | Typ of (typ -> string) * typ
    | Pat of (pat -> string) * pat
    | PatPat of (pat -> pat -> string) * pat * pat
    | PatPatTyp of (pat -> pat -> typ -> string) * pat * pat * typ
    | PatTyp of (pat -> typ -> string) * pat * typ
    | TypTypTyp of (typ -> typ -> typ -> string) * typ * typ * typ


  exception Typ_error of Pos.t * typ_error_details

  let typ_error_details_to_string s = match s with
    | TypKind(s, t, k) -> s t k
    | StringTyp(s,m,t) -> s m t
    | FixedString s -> s
    | String(s, m) -> s m
    | TypTyp(s, t1, t2) -> s t1 t2
    | NumNum(s, d1, d2) -> s d1 d2
    | Typ(s, t) -> s t
    | Pat(s, p) -> s p
    | PatPat(s, p1, p2) -> s p1 p2
    | PatPatTyp(s, p1, p2, t) -> s p1 p2 t
    | PatTyp(s, p, t) -> s p t
    | TypTypTyp(s, t1, t2, t3) -> s t1 t2 t3
  let typ_mismatch p s = 
    if !error_on_mismatch then
      raise (Typ_error (p, s))
    else
      begin
        incr num_typ_errors;
        eprintf "type error at %s : %s\n" (Pos.toString p) (typ_error_details_to_string s)
      end

  (* Necessary for equi-recursive subtyping. *)
  module TypPair = struct
    (* type s = typ * typ *)
    type t = typ * typ
    let compare = Pervasives.compare
  end
  module TPMap = Set.Make (TypPair) (* to fix *)
  module TPMapExt = SetExt.Make (TPMap)


  
  let expose_arrow env typ = 
    let clear_id t = match t with TId x -> (try fst2 (lookup_typ env x) with Not_found -> t) | _ -> t in
    let opt_clear_id t = match t with None -> None | Some t -> Some (clear_id t) in
    match typ with
    | TArrow(args, varargs, ret) -> TArrow(map clear_id args, opt_clear_id varargs, clear_id ret)
    | _ -> typ










  let pat_env (env : env) : pat IdMap.t =
    let select_pat_bound (x, b) = match Ext.extract_b b with
      | BTypBound(TRegex p, _) -> Some (x, p)
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

  exception Not_subtype of typ_error_details

  let mismatched_typ_exn t1 t2 =
    (* Printf.printf "*** Not subtypes: %s </: %s\n" (string_of_typ t1) (string_of_typ t2); *)
    raise (Not_subtype 
       (TypTyp((fun t1 t2 -> sprintf " %s is not a subtype of %s"
         (string_of_typ t1) (string_of_typ t2)), t1, t2)))

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

  and subt env (cache : TPMap.t) s t : TPMap.t = 
    if TPMap.mem (s, t) cache then
      cache
    (* workaround for equal: functional value, due to lazy *)
    else if equivalent_typ env s t then
      cache
    else
      let simpl_s = expose env (simpl_typ env s) in
      let simpl_t = expose env (simpl_typ env t) in
      if TPMap.mem (simpl_s, simpl_t) cache then cache else
      (* Printf.printf "Checking %s against %s\n" (string_of_typ simpl_s) (string_of_typ simpl_t); *)
      match simpl_s, simpl_t with
      | TUninit t', t2 -> begin match !t' with
        | None -> subt env cache (TPrim "Undef") t2
        | Some t1 -> subt env cache t1 t2
      end
      | t1, TUninit t' -> begin match !t' with
        | None -> subt env cache t1 (TPrim "Undef")
        | Some t2 -> subt env cache t1 t2
      end
      | _ -> let cache = TPMap.add (s, t) cache in match simpl_s, simpl_t with
        | TUninit _, _
        | _, TUninit _ -> failwith "Should not be possible!"
        | TRegex pat1, TRegex pat2 ->
          (* Printf.eprintf "Is %s <?: %s == " (Pat.pretty pat1) (Pat.pretty pat2); *)
          if Pat.is_subset (pat_env env) pat1 pat2 then begin
            (* Printf.eprintf "yes\n"; *)
            cache
          end else begin
              (* Printf.eprintf "no: \"%s\"\n" (match (Pat.example (Pat.subtract pat1 pat2)) with *)
              (* | None -> "CONTRADICTION!" *)
              (* | Some s -> s);  *)
              mismatched_typ_exn (TRegex pat1) (TRegex pat2)
            end
        | _, TInter (_, t1, t2) -> (* order matters -- right side must be split first! *)
            subt env (subt env cache s t1) s t2
        | TInter (_, s1, s2), _ -> 
          begin 
            try subt env cache s1 t
            with Not_subtype _ -> subt env cache s2 t
          end
        | TUnion (_, s1, s2), _ -> (* order matters -- left side must be split first! *)
          subt env (subt env cache s1 t) s2 t
        | _, TUnion (_, t1, t2) ->
          begin 
            try subt env cache s t1
            with Not_subtype _ -> subt env cache s t2
          end
        | _, TThis(TPrim "Unsafe") -> cache (* Can always mask the this parameter as Unsafe *)
        | TPrim "Null", TRef (_, TObject _)
        | TPrim "Null", TSource (_, TObject _)
        | TPrim "Null", TSink (_, TObject _) -> cache (* null should be a subtype of all object types *)
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
        | TThis _, TThis _ -> mismatched_typ_exn s t
        | _, TThis t2 -> subt env cache s t2
        | TThis t1, _ -> subt env cache t1 t
        | TArrow (args1, v1, r1), TArrow (args2, v2, r2) ->
          begin
            match v1, v2 with
            | None, None ->
              (try List.fold_left2 (subt env) cache (r1 :: args2) (r2 :: args1)
               with Invalid_argument _ -> mismatched_typ_exn s t)
            | Some v1, Some v2 ->
              (try List.fold_left2 (subt env) cache (r1 :: args2 @ [v2]) (r2 :: args1 @ [v1])
               with Invalid_argument _ -> mismatched_typ_exn s t)
            | _ -> mismatched_typ_exn s t
          end
        | TId x, t -> 
          (try
             subt env cache (fst2 (lookup_typ env x)) t
           with Not_found -> Printf.printf "Cannot find %s in environment\n" x; raise Not_found)
        | t, TId x -> 
          (try
             subt env cache t (fst2 (lookup_typ env x))
           with Not_found -> Printf.printf "Cannot find %s in environment\n" x; raise Not_found)
        | TObject obj1, TObject obj2 ->
            subtype_object env cache obj1 obj2
        | TRef (_, s'), TRef (_, t') -> subt env (subt env cache s' t') t' s'
        | TSource (_, s), TSource (_, t) -> subt env cache s t
        | TSink (_, s), TSink (_, t) -> subt env cache t s
        | TRef (_, s), TSource (_, t) -> subt env cache s t
        | TRef (_, s), TSink (_, t) -> subt env cache t s
        | TForall (_, x1, s1, t1), TForall (_, x2, s2, t2) -> 
          (* Kernel rule *)
          (* TODO: ensure s1 = s2 *)
          let cache' = subt env (subt env cache s1 s2) s2 s1 in
          let t2 = subst (Some x2) (TId x1) (fun x -> x) t2 in
          let env' = IdMap.add x1 (Ext.embed_b (BTypBound (s1, KStar))) env in
          subt env' cache' t1 t2
        | _, TTop -> cache
        | TBot, _ -> cache
        | TLambda (_, [(x, KStar)], s), TLambda (_, [(y, KStar)], t) ->
          let env = IdMap.add x (Ext.embed_b (BTypBound (TTop, KStar))) env in
          let env = IdMap.add y (Ext.embed_b (BTypBound (TTop, KStar))) env in
          subt env cache s t
        | _ -> mismatched_typ_exn s t

  (* Check that an "extra" field is inherited *)
  and check_inherited env cache lang other_proto typ =
    subt env cache typ (inherits Pos.dummy env other_proto lang)

  and subtype_presence prop1 prop2 = match prop1, prop2 with
    | Present, Present 
    | Maybe, Maybe
    | Inherited, Inherited
    | Present , Maybe
    | Present, Inherited -> ()
    | _, _ -> raise (Not_subtype (FixedString"incompatible presence annotations"))

  and subtype_object env cache obj1 obj2 : TPMap.t =
    let lhs_absent = absent_pat obj1 in
    let rhs_absent = absent_pat obj2 in
    let check_simple_overlap ((pat1, pres1, t1), (pat2, pres2, t2)) cache = 
      if Pat.is_overlapped pat1 pat2 then
        begin
          subtype_presence pres1 pres2;
          (* Printf.printf "%s overlaps %s; checking subtypes of %s <: %s\n" *)
          (*   (Pat.pretty pat1) (Pat.pretty pat2) (string_of_typ t1) (string_of_typ t2); *)
          subt env cache t1 t2
        end
      else
        cache in
    let check_pat_containment () =
      (if not (Pat.is_subset (pat_env env) (possible_field_cover_pat obj2) 
                           (cover_pat obj1)) then
         match Pat.example (Pat.subtract (possible_field_cover_pat obj2)
                                     (cover_pat obj1)) with
         | Some ex -> raise (Not_subtype
                               (FixedString("fields on the RHS that are not on the LHS, e.g. " ^ ex ^ 
                                   "; cover_pat obj1 = " ^ (Pat.pretty (cover_pat obj1)) ^
                                   "; possible_pat obj1 = " ^ (Pat.pretty (possible_field_cover_pat obj1)))))
         | None -> failwith "error building counterexample for (2)");
      (if not (Pat.is_subset (pat_env env) rhs_absent lhs_absent); 
          then raise (Not_subtype (FixedString "subtype_object: violated 2-2"))) in
    let check_lhs_absent_overlap (rhs_pat, rhs_pres, rhs_prop) = 
      if Pat.is_overlapped rhs_pat lhs_absent then
        match rhs_pres with
          | Maybe | Inherited -> ()
          | _ -> raise (Not_subtype (FixedString "check_lhs_absent_overlap: LHS absent, RHS present")) in
    let check_rhs_inherited (rhs_pat, rhs_pres, rhs_typ) cache = 
      match rhs_pres with
      | Inherited -> 
          let lhs_typ = inherits Pos.dummy env (TObject obj1) rhs_pat in
          subt env cache lhs_typ rhs_typ
      | _ -> cache in
    (* try  *)
      let cache = 
        L.fold_right check_simple_overlap (L.pairs obj1.fields obj2.fields)
          cache in
      check_pat_containment ();
      L.iter check_lhs_absent_overlap obj2.fields;
      fold_right check_rhs_inherited obj2.fields cache
    (* with Not_subtype m -> *)
    (*   Printf.eprintf "Subtype failed for %s </: %s because\n%s\n" *)
    (*     (string_of_typ (TObject obj1)) (string_of_typ (TObject obj2)) (typ_error_details_to_string m); *)
    (*   raise (Not_subtype m) *)

  and subtypes env ss ts = 
    try 
      let _ = List.fold_left2 (subt env) TPMap.empty ss ts in
      true
    with 
      | Invalid_argument _ -> false (* unequal lengths *)
      | Not_subtype _ -> false

  and cache : (* bool  *)TPMap.t ref = ref TPMap.empty 
  and subtype env s t = 
    try
      cache := subt env !cache s t;
      true
    with 
      | Not_subtype str -> false

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
