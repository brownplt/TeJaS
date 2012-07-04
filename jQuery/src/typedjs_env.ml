open Prelude
open Sig
open Strobe_sigs

module Make
  (Strobe : STROBE_MODULE)
  (StrobeKinding : STROBE_KINDING
   with type typ = Strobe.typ
  with type kind = Strobe.kind
  with type binding = Strobe.binding
  with type extBinding = Strobe.extBinding
  with type extTyp = Strobe.extTyp
  with type extKind = Strobe.extKind
  with type env = Strobe.env)
  (Desugar : Typedjs_desugar.DESUGAR with type typ = Strobe.extTyp with type kind = Strobe.extKind)
  : (TYP_ENV
     with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type env = Strobe.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl) =
struct
  type typ = Strobe.extTyp
  type kind = Strobe.extKind
  type binding = Strobe.extBinding
  type env = Strobe.env
  type env_decl = Typedjs_writtyp.WritTyp.env_decl

  open Strobe
  module W = Typedjs_writtyp.WritTyp
  module List = ListExt
  exception Not_wf_typ of string

  let desugar_typ pos t = Strobe.Ext.extract_t (Desugar.desugar_typ pos t)

  let print_env env fmt : unit =
    FormatExt.braces (Strobe.Pretty.env env) fmt;
    Format.pp_print_flush fmt ()

  let bind x b env = IdMap.add x b env
  let bind' x b env = bind x (Strobe.Ext.embed_b b) env
  let bind_id x t env = bind' x (BTermTyp t) env

  open Lexing

  let parse_env_buf lexbuf name =
    try
      lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with 
        Lexing.pos_fname = name };
      Typedjs_parser.env Typedjs_lexer.token lexbuf
    with
    | Failure "lexing: empty token" ->
      failwith (sprintf "error lexing environment at %s"
                  (Pos.rangeToString
                     lexbuf.lex_curr_p lexbuf.lex_curr_p))
    | Typedjs_parser.Error ->
      failwith (sprintf "error parsing environment at %s"
                  (Pos.rangeToString
                     lexbuf.lex_curr_p lexbuf.lex_curr_p))
  let parse_env text name =
    let lexbuf = Lexing.from_string text in
    parse_env_buf lexbuf name
  let parse_env_file (cin : in_channel) (name : string) : env_decl list =
    let lexbuf = Lexing.from_channel cin in
    parse_env_buf lexbuf name


  let extend_global_env env lst =
    let rec add recIds env decl = match decl with
      | W.EnvBind (p, x, typ) ->
        if IdMap.mem x env then
          raise (Not_wf_typ (x ^ " is already bound in the environment"))
        else
          let t = expose_twith env (desugar_typ p typ) in
        (* Printf.eprintf "Binding type for %s to %s\n" x (string_of_typ t); *)
          bind_id x t env
      | W.EnvType (p, x, writ_typ) ->
        if IdMap.mem x env then
          raise (Not_wf_typ (sprintf "the type %s is already defined" x))
        else
          let t = expose_twith env (desugar_typ p writ_typ) in
        (* Printf.eprintf "Binding %s to %s\n" x (string_of_typ (apply_name (Some x) t)); *)
          let k = StrobeKinding.kind_check env recIds t in
          bind' x (BTypBound(apply_name (Some x) t, k)) env
      | W.EnvPrim (p, s) ->
        StrobeKinding.new_prim_typ s;
        env
      | W.ObjectTrio(pos, (c_id, c_typ), (p_id, p_typ), (i_id, i_typ)) ->
      (* add prototype field to constructor *)
        let c_typ = expose_twith env (desugar_typ pos c_typ) in
        let c_absent_pat = match c_typ with TRef(_, TObject(f)) -> absent_pat f | _ -> Pat.all in
        let constructor_with = TWith(c_typ, (mk_obj_typ
                                               [Pat.singleton "prototype", Present,
                                                TApp(TPrim("Mutable"), [TId(p_id)])]
                                               (Pat.subtract c_absent_pat (Pat.singleton "prototype")))) in
        let constructor = replace_name (Some c_id) (expose_twith env constructor_with) in
        (* add constructor field to prototype *)
        let p_typ = (desugar_typ pos p_typ) in
        let p_typ = match p_typ with TId _ -> simpl_typ env p_typ | _ -> p_typ in
        let (prototype_added_fields, prototype_with) = match p_typ with
          | TWith(base, f) ->
            (fields f), TWith(base, (mk_obj_typ
                                       ((Pat.singleton "constructor", Maybe, TId(c_id))::(fields f))
                                       (Pat.subtract (absent_pat f) (Pat.singleton "constructor"))))
          | TRef(_, TObject(f))
          | TSource(_, TObject(f)) ->
            let temp =
              (expose_twith env
                 (TWith(TId("AnObject"),
                        (mk_obj_typ
                           [Pat.singleton "constructor", Present, TId(c_id)]
                           (Pat.subtract (absent_pat f) (Pat.singleton "constructor")))))) in
            (fields f), TWith(temp, (mk_obj_typ (fields f) (Pat.subtract (absent_pat f) (Pat.singleton "constructor"))))
          | _ -> failwith "impossible" in
        let prototype = match expose_twith env prototype_with with TRef (n, t) -> TSource(n, t) | t -> t in
        (* add __proto__ field to instance *)
        let i_typ = (desugar_typ pos i_typ) in
        let i_typ = match i_typ with TId _ -> simpl_typ env i_typ | _ -> i_typ in
        let instance_with =
          let proto_fields = List.map (fun (n, _, t) -> (n, Inherited, t)) prototype_added_fields in
          let proto_field_pat = Pat.unions (proto_pat::(List.map fst3 prototype_added_fields)) in
          match i_typ with
          | TWith(base, f) ->
            let absent_pat = absent_pat f in
            let new_fields = List.filter (fun (p, _, _) -> not (Pat.is_empty p)) (List.map (fun (pat, p, t) ->
              (Pat.subtract (Pat.subtract pat proto_field_pat) absent_pat, p, t))
                                                                                    (fields f)) in
            TWith(base, mk_obj_typ ((proto_pat, Present, TId(p_id))::proto_fields@new_fields) absent_pat)
          | TRef(_, TObject(f))
          | TSource(_, TObject(f)) ->
            let absent_pat = Pat.subtract (absent_pat f) proto_field_pat in
            let base_fields = List.filter (fun (p, _, _) -> not (Pat.is_empty p)) (List.map (fun (pat, p, t) ->
              (Pat.subtract (Pat.subtract pat proto_field_pat) absent_pat, p, t))
                                                                                     (fields f)) in
            TWith(TId "AnObject",
                  (mk_obj_typ ((proto_pat, Present, TId(p_id))::proto_fields@base_fields) absent_pat))
          | _ -> failwith "impossible" in
        let instance = replace_name (Some i_id) (expose_twith env instance_with) in
        let (k_c, k_p, k_i) = (StrobeKinding.kind_check env [c_id; p_id; i_id] constructor,
                               StrobeKinding.kind_check env [c_id; p_id; i_id] prototype,
                               StrobeKinding.kind_check env [c_id; p_id; i_id] instance) in
        (bind' c_id (BTypBound(constructor, k_c))
           (bind' p_id (BTypBound(prototype, k_p))
              (bind' i_id (BTypBound(instance, k_i)) env)))
      | W.RecBind (binds) ->
        let ids = List.concat (List.map (fun b -> match b with
          | W.EnvBind (_, x, _) -> [x]
          | W.EnvType (_, x, _) -> [x]
          | W.ObjectTrio(_, (c, _), (p, _), (i, _)) -> [c;p;i]
          | W.EnvPrim _
          | W.RecBind _ -> []) binds) in
        Printf.eprintf "Recursively including ids: ";
        List.iter (fun x -> Printf.eprintf "%s " x) ids;
        List.fold_left (add ids) env binds
    in List.fold_left (add []) env lst

  let extend_global_env env lst = failwith "STROBE: Extend_global_env Not implemented"
  let set_global_object env cname = failwith "STROBE: Set_global_object Not implemented"

(* let apply_subst subst typ = IdMap.fold typ_subst subst typ *)


(* (\* Quick hack to infer types; it often works. Sometimes it does not. *\) *)
(* let assoc_merge = IdMap.merge (fun x opt_s opt_t -> match opt_s, opt_t with *)
(*   | Some (TId y), Some (TId z) ->  *)
(*     if x = y then opt_t else opt_s *)
(*   | Some (TId _), Some t  *)
(*   | Some t, Some (TId _) -> Some t *)
(*   | Some t, _ *)
(*   | _, Some t -> *)
(*     Some t *)
(*   | None, None -> None) *)


(* let rec typ_assoc (env : env) (typ1 : typ) (typ2 : typ) =  *)
(*   match (typ1, typ2) with *)
(*     | TId x, _ -> IdMap.singleton x typ2 *)
(*     | TApp (s1, [s2]), TApp (t1, [t2]) *)
(*     | TInter (_, s1, s2), TInter (_, t1, t2) *)
(*     | TUnion (_, s1, s2), TUnion (_, t1, t2) ->  *)
(*       assoc_merge (typ_assoc env s1 t1) (typ_assoc env s2 t2) *)

(*     | TApp (s1, s2), t *)
(*     | t, TApp (s1, s2) -> *)
(*       typ_assoc env (simpl_typ env (TApp (s1, s2))) t *)

(*     | TObject o1, TObject o2 -> *)
(*       let flds1 = fields o1 in *)
(*       let flds2 = fields o2 in *)
(*       List.fold_left assoc_merge *)
(*         IdMap.empty *)
(*         (List.map2_noerr (fld_assoc env) flds1 flds2) *)
(*     | TSource (_, s), TSource (_, t) *)
(*     | TSink (_, s), TSink (_, t) *)
(*     | TRef (_, s), TRef (_, t) -> *)
(*       typ_assoc env s t *)
(*     | TArrow (args1, v1, r1), TArrow (args2, v2, r2) -> *)
(*       List.fold_left assoc_merge *)
(*         ((fun base -> match v1, v2 with *)
(*         | Some v1, Some v2 -> assoc_merge (typ_assoc env v1 v2) base *)
(*         | _ -> base) *)
(*             (typ_assoc env r1 r2)) *)
(*         (List.map2_noerr (typ_assoc env) args1 args2) *)
(*     | TRec (_, x, s), TRec (_, y, t) -> *)
(*       (\* could do better here, renaming*\) *)
(*       typ_assoc env s t *)
(*     | TForall (_, x, s1, s2), TForall (_, y, t1, t2) -> *)
(*       (\* also here *\) *)
(*       assoc_merge (typ_assoc env s1 t1) (typ_assoc env s2 t2) *)
(*     | _ -> IdMap.empty *)

(* and fld_assoc env (_, _, s) (_, _, t) = typ_assoc env s t *)

(* let tid_env env = env.typ_ids *)

(* let typid_env env = IdMap.map (fun (t, _) -> t) env.typ_ids *)


(* let extend_env (trm_vars : typ IdMap.t) (typ_vars : (typ * kind) IdMap.t) env = *)
(*   let merge_fn toStr x left right = match (left, right) with *)
(*     | Some t1, Some t2 -> failwith (sprintf "rebinding %s in the environment: currently has type %s and trying to add type %s" x (toStr t1) (toStr t2)) *)
(*     | None, Some t *)
(*     | Some t, None -> Some t *)
(*     | None, None -> failwith "impossible case in extend_env" in *)
(*   { env with id_typs = IdMap.merge (merge_fn string_of_typ) env.id_typs trm_vars; *)
(*     typ_ids = IdMap.merge (merge_fn (fun (t, _) -> string_of_typ t)) env.typ_ids typ_vars } *)

(* let verify_env env : unit = *)
(*   let errors = ref false in *)
(*   let kinding_env = IdMap.map (fun (_, k) -> k) env.typ_ids in *)
(*   let f x (t, k) = *)
(*     let k' = Sb_kinding.kind_check kinding_env [] t in *)
(*     if k = k' then *)
(*       () *)
(*     else *)
(*       begin *)
(*         printf "%s declared kind is %s, but calculated kind is %s.\n\ *)
(*                 Type of %s is:\n%s\n" *)
(*           x (string_of_kind k) (string_of_kind k') x (string_of_typ t); *)
(*         errors := true *)
(*       end in *)
(*   IdMap.iter f env.typ_ids *)
(* (\*  *)
(*      if !errors then *)
(*      raise (Invalid_argument "ill-formed environment") *)
(*   *\) *)

(* let kind_check env (typ : typ) : kind  =  kind_check env [] typ *)
end
