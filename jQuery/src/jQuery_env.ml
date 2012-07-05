open Prelude
open Sig
open Strobe_sigs
open JQuery_sigs

module List = ListExt
exception Not_wf_typ of string

module MakeExt
  (JQuery : JQUERY_MODULE)
  (JQueryKinding : JQUERY_KINDING
   with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type multiplicity = JQuery.multiplicity
  with type sigma = JQuery.sigma
  with type binding = JQuery.binding
  with type baseTyp = JQuery.baseTyp
  with type baseKind = JQuery.baseKind
  with type baseBinding = JQuery.baseBinding
  with type env = JQuery.env) 
  (Env : TYP_ENV
   with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type binding = JQuery.binding
  with type env = JQuery.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
  (Desugar : Typedjs_desugar.DESUGAR
   with type typ = JQuery.typ
  with type kind = JQuery.kind)
  : (JQUERY_TYP_ENV
     with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type sigma = JQuery.sigma
  with type multiplicity = JQuery.multiplicity
  with type binding = JQuery.binding
  with type env = JQuery.env
  with type env_decl = Env.env_decl) =
struct
  type typ = Env.typ
  type kind = Env.kind
  type binding = Env.binding
  type sigma = JQuery.sigma
  type multiplicity = JQuery.multiplicity
  type env = Env.env
  type env_decl = Env.env_decl
  open Env
  open JQueryKinding
  module Strobe = JQuery.Strobe

  let print_env = Env.print_env
  let parse_env_buf = Env.parse_env_buf
  let parse_env = Env.parse_env
  let parse_env_file = Env.parse_env_file
  let lookup_lbl = Env.lookup_lbl
  let clear_labels = Env.clear_labels

  let bind x b (env : env) : env = 
    let bs = try IdMap.find x env with Not_found -> [] in
    let bs = List.filter (fun b' -> match embed_b (extract_b b'), b with
      | BMultBound _, BMultBound _
      | BStrobe (Strobe.BTermTyp _), BStrobe (Strobe.BTermTyp _)
      | BStrobe (Strobe.BTypBound _), BStrobe (Strobe.BTypBound _)
      | BStrobe (Strobe.BLabelTyp _), BStrobe (Strobe.BLabelTyp _) -> false
      | _ -> true) bs in
    IdMap.add x (b::bs) env
  let bind' x b (env : env) = bind x (JQuery.embed_b b) env
  let bind_id x t (env : env) = bind' x (Strobe.BTermTyp (JQuery.extract_t t)) env
  let bind_lbl x t env = bind' x (Strobe.BLabelTyp (JQuery.extract_t t)) env
  let raw_bind_typ_id x t k (env : env) = bind' x (Strobe.BTypBound (t, k)) env
  let raw_bind_mult_id x t m (env : env) = bind x (BMultBound (t, m)) env

  let kind_check env recIds (s : sigma) : kind  =
    JQueryKinding.kind_check_sigma env recIds s

  let bind_rec_typ_id (x : id) recIds (s : sigma) (env : env) = 
    let k = kind_check env recIds s in
    match s with
    | STyp t -> raw_bind_typ_id x (JQuery.extract_t t) (JQuery.extract_k k) env
    | SMult m -> raw_bind_mult_id x m k env

  let bind_typ_id x t env = bind_rec_typ_id x [] (STyp t) env
  let bind_mult_id x m env = bind_rec_typ_id x [] (SMult m) env

  let bind_recursive_types (xts : (id * typ) list) (env : env) =
    let env' = List.fold_left (fun ids (x, t) -> 
      raw_bind_typ_id x (JQuery.extract_t t) Strobe.KStar ids) env xts in
    timefn "Bindrec/Kind checking" (List.fold_left (fun env (x, t) -> bind_typ_id x t env) env') xts

  let unchecked_bind_typ_ids (xts : (id * typ) list) (env : env) =
    List.fold_left (fun ids (x, t) -> raw_bind_typ_id x (JQuery.extract_t t) Strobe.KStar ids) env xts

  let lookup_id x env = Env.lookup_id x env

  let lookup_typ_id x env = Env.lookup_typ_id x env

  let lookup_mult_id x (env : env) =
    let bs = IdMap.find x env in
    match (ListExt.filter_map (fun b -> match (embed_b (extract_b b)) with
    | BMultBound (m,_) -> Some m
    | _ -> None) bs) with
    | [m] -> m
    | _ -> raise Not_found

  let rec set_global_object (env : env) cname =
    let (ci_typ, ci_kind) = 
      try lookup_typ_id cname env
      with Not_found -> 
        raise (Not_wf_typ ("global object, " ^ cname ^ ", not found")) in
    match (Strobe.expose env (Strobe.simpl_typ env (extract_t ci_typ)), extract_k ci_kind) with
    | Strobe.TRef (n, Strobe.TObject o), Strobe.KStar ->
      let fs = Strobe.fields o in
      let add_field env (x, pres, t) =
        if pres = Strobe.Present then
          match Strobe.Pat.singleton_string x with
          | Some s -> bind_id s (JQuery.embed_t (Strobe.TRef (n, t))) env
          | None -> 
            raise (Not_wf_typ (cname ^ " field was a regex in global"))
        else
          raise (Not_wf_typ "all fields on global must be present") in
      List.fold_left add_field env fs
    | t, _ -> raise (Not_wf_typ (cname ^ " global must be an object, got\n" ^
                                   string_of_typ (embed_t t)))


  let extend_global_env env lst =
    let desugar_typ p t = JQuery.extract_t (Desugar.desugar_typ p t) in
    let open Typedjs_writtyp.WritTyp in
    let rec add recIds env decl = match decl with
      | EnvBind (p, x, typ) ->
        (try 
           ignore (lookup_id x env);
           raise (Not_wf_typ (x ^ " is already bound in the environment"))
         with Not_found ->
           let t = JQuery.embed_t (Strobe.expose_twith env (desugar_typ p typ)) in
           (* Printf.eprintf "Binding type for %s to %s\n" x (string_of_typ t); *)
           bind_id x t env)
      | EnvType (p, x, writ_typ) ->
        (try
           ignore (lookup_typ_id x env);
           raise (Not_wf_typ (sprintf "the type %s is already defined" x))
         with Not_found ->
           let t = Strobe.expose_twith env (desugar_typ p writ_typ) in
           (* Printf.eprintf "Binding %s to %s\n" x (string_of_typ (apply_name (Some x) t)); *)
           let k = kind_check env recIds (STyp (embed_t t)) in
           raw_bind_typ_id x (extract_t (apply_name (Some x) (embed_t t))) (extract_k k) env)
      | EnvPrim (p, s) ->
        JQueryKinding.new_prim_typ s;
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
        let (k_c, k_p, k_i) = (kind_check env [c_id; p_id; i_id] (STyp constructor),
                               kind_check env [c_id; p_id; i_id] (STyp prototype),
                               kind_check env [c_id; p_id; i_id] (STyp instance)) in
        (raw_bind_typ_id c_id (extract_t constructor) (extract_k k_c)
           (raw_bind_typ_id p_id (extract_t prototype) (extract_k k_p)
              (raw_bind_typ_id i_id (extract_t instance) (extract_k k_i) env)))
      | RecBind (binds) ->
        let ids = List.concat (List.map (fun b -> match b with
          | EnvBind (_, x, _) -> [x]
          | EnvType (_, x, _) -> [x]
          | ObjectTrio(_, (c, _), (p, _), (i, _)) -> [c;p;i]
          | EnvPrim _
          | RecBind _ -> []) binds) in
        Printf.eprintf "Recursively including ids: ";
        List.iter (fun x -> Printf.eprintf "%s " x) ids;
        List.fold_left (add ids) env binds
    in List.fold_left (add []) env lst

  (* let rec bind_typ env typ : env * typ = match typ with *)
  (*   | TForall (n, x, s, t) -> bind_typ (bind_typ_id x s env) (apply_name n t) *)
  (*   | typ -> (env, typ) *)
end
