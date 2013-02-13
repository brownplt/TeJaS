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
   (Desugar : DESUGAR with type typ = Strobe.extTyp
                 with type writtyp = Typedjs_writtyp.WritTyp.t)
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
    FormatExt.label_braces "Environment: " FormatExt.cut (Strobe.Pretty.env env) fmt;
    Format.pp_print_flush fmt ()

  let bind x (b : Strobe.extBinding) (env : env) : env = 
    let bs = try IdMap.find x env with Not_found -> [] in
    let bs = List.filter (fun b' -> match Ext.extract_b b', Ext.extract_b b with
      | BTermTyp _, BTermTyp _
      | BTypDef _, BTypDef _
      | BTypBound _, BTypBound _
      | BTyvar _, BTyvar _
      | BLabelTyp _, BLabelTyp _
      | BEmbed _, BEmbed _ -> false
      | _ -> true) bs in
    IdMap.add x (b::bs) env
  let bind' x b env = bind x (Ext.embed_b b) env
  let bind_id x t env = bind' x (BTermTyp (Ext.extract_t t)) env
  let bind_lbl x t env = bind' x (BLabelTyp (Ext.extract_t t)) env


  let bind_rec_typ_id (x : id) recIds (t : extTyp) (env : env) = 
    let k = StrobeKinding.kind_check env recIds (Ext.extract_t t) in
    bind' x (BTypBound(Ext.extract_t t, k)) env

  let bind_typ_id x t env = bind_rec_typ_id x [] t env


  let lookup_id x (env : env) = 
    let bs = IdMap.find x env in
    match (ListExt.filter_map (fun b -> match Ext.extract_b b with
    | BTermTyp t -> Some (Ext.embed_t t)
    | _ -> None) bs) with
    | [t] -> t
    | _ -> ((* Printf.eprintf "Couldn't find %s in lookup_id\n" x; *) raise Not_found)

  let lookup_typ_alias x env =
    let bs = IdMap.find x env in
    match (ListExt.filter_map (fun b -> match Ext.extract_b b with
    | BTypDef (t,k) -> Some (Ext.embed_t t, Ext.embed_k k)
    | _ -> None) bs) with
    | [tk] -> tk
    | _ -> ((* Printf.eprintf "Couldn't find %s in lookup_typ_alias\n" x; *) raise Not_found)

  let lookup_typ_id x env =
    let bs = IdMap.find x env in
    match (ListExt.filter_map (fun b -> match Ext.extract_b b with
    | BTypBound (t,k) -> Some (Ext.embed_t t, Ext.embed_k k)
    | _ -> None) bs) with
    | [tk] -> tk
    | _ -> ((* Printf.eprintf "Couldn't find %s in lookup_typ_id\n" x; *) raise Not_found)


  let lookup_lbl x (env : env) = 
    let bs = IdMap.find x env in
    match (ListExt.filter_map (fun b -> match Ext.extract_b b with
    | BLabelTyp t -> Some (Ext.embed_t t)
    | _ -> None) bs) with
    | [t] -> t
    | _ -> ((* Printf.eprintf "Couldn't find %s in lookup_lbl\n" x; *) raise Not_found)

  let clear_labels env =
    let env' = IdMap.map 
      (fun bs -> List.filter (fun b -> match Ext.extract_b b with BLabelTyp _ -> false | _ -> true) bs) env in
    try
      bind_lbl "%return" (lookup_lbl "%return" env) env'
    with Not_found -> env'

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
      | W.Decl _ -> env
      | W.EnvBind (p, x, typ) ->
        (try
           ignore (lookup_id x env);
           raise (Not_wf_typ (x ^ " is already bound in the environment"))
         with Not_found ->
           let t = expose_twith env (desugar_typ p typ) in
           (* Printf.eprintf "Binding type for %s to %s\n" x (string_of_typ t); *)
           bind_id x (Ext.embed_t t) env)
      | W.EnvType (p, x, writ_typ) ->
        Printf.eprintf "Trying to bind alias %s\n" x;
        (try 
           ignore (lookup_typ_alias x env);
           raise (Not_wf_typ (sprintf "the type %s is already defined" x))
         with Not_found ->
           let t = expose_twith env (desugar_typ p writ_typ) in
           Printf.eprintf "Binding %s to %s\n" x (string_of_typ (apply_name (Some x) t));
           let k = StrobeKinding.kind_check env recIds t in
           bind' x (BTypDef(apply_name (Some x) t, k)) env)
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
        (bind' c_id (BTypDef(constructor, k_c))
           (bind' p_id (BTypDef(prototype, k_p))
              (bind' i_id (BTypDef(instance, k_i)) env)))
      | W.RecBind (binds) ->
        let ids = List.concat (List.map (fun b -> match b with
          | W.EnvBind (_, x, _) -> [x]
          | W.EnvType (_, x, _) -> [x]
          | W.ObjectTrio(_, (c, _), (p, _), (i, _)) -> [c;p;i]
          | W.Decl _
          | W.EnvPrim _
          | W.RecBind _ -> []) binds) in
        (* Printf.eprintf "Recursively including ids: "; *)
        (* List.iter (fun x -> Printf.eprintf "%s " x) ids; *)
        List.fold_left (add ids) env binds
    in List.fold_left (add []) env lst

  let extend_global_env env lst = failwith "STROBE: Extend_global_env Not implemented"
  let set_global_object env cname = failwith "STROBE: Set_global_object Not implemented"
end
