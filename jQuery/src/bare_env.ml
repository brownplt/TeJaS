open Prelude
open Sig
open Strobe_sigs
open Bare_sigs

module List = ListExt
exception Not_wf_typ of string

module MakeExt
  (Bare : BARE_MODULE)
  (BareKinding : BARE_KINDING
   with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)
  (Env : TYP_ENV
   with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type env = Bare.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
  (Desugar : Bare_desugar.BARE_DESUGAR
   with type typ = Bare.typ
   with type writtyp = Typedjs_writtyp.WritTyp.t
  with type kind = Bare.kind)
  : (BARE_TYP_ENV
     with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type env = Bare.env
  with type env_decl = Env.env_decl) =
struct
  type typ = Env.typ
  type kind = Env.kind
  type binding = Env.binding
  type env = Env.env
  type env_decl = Env.env_decl
  open Env
  open BareKinding

  module Strobe = Bare.Strobe

  let use_strict_selections = ref false

  let do_use_strict_selections () = use_strict_selections := true

  let print_env env fmt =
    Env.print_env env fmt

  let parse_env_buf = Env.parse_env_buf
  let parse_env = Env.parse_env
  let parse_env_file = Env.parse_env_file
  let lookup_lbl = Env.lookup_lbl
  let clear_labels = Env.clear_labels

  (* This allows bindings of the same name to different types of
     bindings; an alternate implementation would just shadow and
     drop all existing bindings. *)
  let bind x b (env : env) : env =
    let bs = try IdMap.find x env with Not_found -> [] in
    let bs = List.filter (fun b' -> match unwrap_b b', b with
      | BStrobe (Strobe.BTermTyp _), BStrobe (Strobe.BTermTyp _)
      | BStrobe (Strobe.BTypDef _), BStrobe (Strobe.BTypDef _)
      | BStrobe (Strobe.BTypBound _), BStrobe (Strobe.BTypBound _)
      | BStrobe (Strobe.BTyvar _), BStrobe (Strobe.BTyvar _)
      | BStrobe (Strobe.BLabelTyp _), BStrobe (Strobe.BLabelTyp _) -> false
      | _ -> true) bs in
    IdMap.add x (b::bs) env

  let bind' x b (env : env) = bind x (Bare.embed_b b) env
  let bind_id x t (env : env) = bind' x (Strobe.BTermTyp (Bare.extract_t t)) env
  let bind_lbl x t env = bind' x (Strobe.BLabelTyp (Bare.extract_t t)) env

  let bind_typdef x t k env = bind' x (Strobe.BTypDef (t, k)) env

  let raw_bind_typ_id x t k (env : env) = bind' x (Strobe.BTypBound (t, k)) env

  let bind_rec_typ_id (x : id) recIds (t : typ) (env : env) =
    let k = kind_check env recIds t in
    raw_bind_typ_id x (Bare.extract_t t) (Bare.extract_k k) env

  let bind_typ_id x t env = bind_rec_typ_id x [] t env

  let bind_recursive_types (xts : (id * typ) list) (env : env) =
    let env' = List.fold_left (fun ids (x, t) ->
      raw_bind_typ_id x (Bare.extract_t t) Strobe.KStar ids) env xts in
    timefn "Bindrec/Kind checking" (List.fold_left (fun env (x, t) -> bind_typ_id x t env) env') xts

  let unchecked_bind_typ_ids (xts : (id * typ) list) (env : env) =
    List.fold_left (fun ids (x, t) -> raw_bind_typ_id x (Bare.extract_t t) Strobe.KStar ids) env xts

  let lookup_id x env = Env.lookup_id x env

  let lookup_typ_id x env = Env.lookup_typ_id x env
  let lookup_typ_alias x env = Env.lookup_typ_alias x env

  let rec set_global_object (env : env) cname =
    let (ci_typ, ci_kind) =
      try lookup_typ_alias cname env
      with Not_found ->
        raise (Not_wf_typ ("global object, " ^ cname ^ ", not found")) in
    match (Strobe.expose env (Strobe.simpl_typ env (extract_t ci_typ)), extract_k ci_kind) with
    | Strobe.TRef (n, Strobe.TObject o), Strobe.KStar ->
      let fs = Strobe.fields o in
      let add_field env (x, pres, t) =
        if pres = Strobe.Present then
          match Strobe.Pat.singleton_string x with
          | Some s -> bind_id s (Bare.embed_t (Strobe.TRef (n, t))) env
          | None ->
            raise (Not_wf_typ (cname ^ " field was a regex in global"))
        else
          raise (Not_wf_typ "all fields on global must be present") in
      List.fold_left add_field env fs
    | t, _ -> raise (Not_wf_typ (cname ^ " global must be an object, got\n" ^
                                   string_of_typ (embed_t t)))


  (* Consumes an env and a list of declarations
     1) Gathers all top level declComps, and desugars them.
     2) Add all non-structure decls into the env *)
  let extend_global_env env lst =
    let open Typedjs_writtyp.WritTyp in

    (* 1) Partition lst into local structure declarations and non-structure
       declarations *)
    let (_, non_structure_decls) =
      List.partition (fun d -> match d with
      | Decl _ -> true | _ -> false) lst in

    (* 2) Then add all non-structure decls to the env *)

    let lst = non_structure_decls in

    let desugar_typ p t = Bare.extract_t (Desugar.desugar_typ p t) in
    let rec add recIds env decl = match decl with
      | EnvBind (p, x, typ) ->
        (try
           ignore (lookup_id x env);
           raise (Not_wf_typ (x ^ " is already bound in the environment"))
         with Not_found ->
           let t = Bare.embed_t (Strobe.expose_twith env (desugar_typ p typ)) in
           (* Printf.eprintf "Binding type for %s to %s\n" x (string_of_typ t); *)
           bind_id x t env)
      | EnvType (p, x, writ_typ) ->
        (try
           ignore (lookup_typ_alias x env);
           raise (Not_wf_typ (sprintf "the type %s is already defined" x))
         with Not_found ->
           let t' = Desugar.desugar_typ p writ_typ in
           let t'' = Bare.expose_twith env t' in
           let k = kind_check env recIds t'' in
           bind_typdef x (extract_t (apply_name (Some x) t'')) (extract_k k) env)
      | EnvPrim (p, s) ->
        BareKinding.new_prim_typ s;
        env
      | ObjectTrio(pos, (c_id, c_typ), (p_id, p_typ), (i_id, i_typ)) ->
        (* add prototype field to constructor *)
        let c_typ = Strobe.expose_twith env (desugar_typ pos c_typ) in
        let c_absent_pat = match c_typ with
          | Strobe.TRef(_, Strobe.TObject(f)) -> Strobe.absent_pat f
          | _ -> Strobe.Pat.all in
        let constructor_with =
          Strobe.TWith(c_typ, (Strobe.mk_obj_typ
                                 [Strobe.Pat.singleton "prototype", Strobe.Present,
                                  Strobe.TApp(Strobe.TPrim("Mutable"), [Strobe.TId(p_id)])]
                                 (Strobe.Pat.subtract c_absent_pat (Strobe.Pat.singleton "prototype")))) in
        let constructor = replace_name (Some c_id) (embed_t (Strobe.expose_twith env constructor_with)) in
        (* add constructor field to prototype *)
        let p_typ = (desugar_typ pos p_typ) in
        let p_typ = match p_typ with Strobe.TId _ -> Strobe.simpl_typ env p_typ | _ -> p_typ in
        let (prototype_added_fields, prototype_with) = match p_typ with
          | Strobe.TWith(base, f) ->
            (Strobe.fields f), Strobe.TWith(base,
                                            (Strobe.mk_obj_typ
                                               ((Strobe.Pat.singleton "constructor", Strobe.Maybe,
                                                 Strobe.TId(c_id))::(Strobe.fields f))
                                               (Strobe.Pat.subtract (Strobe.absent_pat f)
                                                  (Strobe.Pat.singleton "constructor"))))
          | Strobe.TRef(_, Strobe.TObject(f))
          | Strobe.TSource(_, Strobe.TObject(f)) ->
            let temp =
              (Strobe.expose_twith env
                 (Strobe.TWith(Strobe.TId("AnObject"),
                        (Strobe.mk_obj_typ
                           [Strobe.Pat.singleton "constructor", Strobe.Present, Strobe.TId(c_id)]
                           (Strobe.Pat.subtract (Strobe.absent_pat f) (Strobe.Pat.singleton "constructor")))))) in
            (Strobe.fields f), Strobe.TWith(temp,
                                     (Strobe.mk_obj_typ (Strobe.fields f)
                                        (Strobe.Pat.subtract (Strobe.absent_pat f)
                                           (Strobe.Pat.singleton "constructor"))))
          | _ -> failwith "impossible" in
        let prototype = embed_t (match Strobe.expose_twith env prototype_with with
          | Strobe.TRef (n, t) -> Strobe.TSource(n, t)
          | t -> t) in
        (* add __proto__ field to instance *)
        let i_typ = (desugar_typ pos i_typ) in
        let i_typ = match i_typ with Strobe.TId _ -> Strobe.simpl_typ env i_typ | _ -> i_typ in
        let instance_with =
          let proto_fields = List.map (fun (n, _, t) -> (n, Strobe.Inherited, t)) prototype_added_fields in
          let proto_field_pat = Strobe.Pat.unions (Strobe.proto_pat::(List.map fst3 prototype_added_fields)) in
          match i_typ with
          | Strobe.TWith(base, f) ->
            let absent_pat = Strobe.absent_pat f in
            let new_fields =
              List.filter (fun (p, _, _) -> not (Strobe.Pat.is_empty p))
                (List.map (fun (pat, p, t) ->
                  (Strobe.Pat.subtract (Strobe.Pat.subtract pat proto_field_pat) absent_pat, p, t))
                   (Strobe.fields f)) in
            Strobe.TWith(base,
                         Strobe.mk_obj_typ ((Strobe.proto_pat, Strobe.Present, Strobe.TId(p_id))::
                                               proto_fields@new_fields) absent_pat)
          | Strobe.TRef(_, Strobe.TObject(f))
          | Strobe.TSource(_, Strobe.TObject(f)) ->
            let absent_pat = Strobe.Pat.subtract (Strobe.absent_pat f) proto_field_pat in
            let base_fields =
              List.filter (fun (p, _, _) -> not (Strobe.Pat.is_empty p)) (List.map (fun (pat, p, t) ->
                (Strobe.Pat.subtract (Strobe.Pat.subtract pat proto_field_pat) absent_pat, p, t))
                                                                            (Strobe.fields f)) in
            Strobe.TWith(Strobe.TId "AnObject",
                  (Strobe.mk_obj_typ ((Strobe.proto_pat, Strobe.Present, Strobe.TId(p_id))::
                                         proto_fields@base_fields) absent_pat))
          | _ -> failwith "impossible" in
        let instance = replace_name (Some i_id) (embed_t (Strobe.expose_twith env instance_with)) in
        let (k_c, k_p, k_i) = (kind_check env [c_id; p_id; i_id] constructor,
                               kind_check env [c_id; p_id; i_id] prototype,
                               kind_check env [c_id; p_id; i_id] instance) in
        (bind_typdef c_id (extract_t constructor) (extract_k k_c)
           (bind_typdef p_id (extract_t prototype) (extract_k k_p)
              (bind_typdef i_id (extract_t instance) (extract_k k_i) env)))
      | RecBind (binds) ->
        let ids = List.concat (List.map (fun b -> match b with
          | EnvBind (_, x, _) -> [x]
          | EnvType (_, x, _) -> [x]
          | ObjectTrio(_, (c, _), (p, _), (i, _)) -> [c;p;i]
          | Decl _
          | EnvPrim _
          | RecBind _ -> []) binds) in
        (* Printf.eprintf "Recursively including ids: "; *)
        (* List.iter (fun x -> Printf.eprintf "%s " x) ids; *)
        List.fold_left (add ids) env binds
      (* These are unknown cases; to be factored out and replaced with an _ case *)
      | Decl (_, (name,_,_,_,_)) ->
        failwith (sprintf "BARE_extend_global_env: impossible: all local structure declarations should have already been compiled, but Decl %s was not." name)

    in

    List.fold_left (add []) env lst


  (* End of extend_global_env *)

end
