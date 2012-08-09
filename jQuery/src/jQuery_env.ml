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
  with type sel = JQuery.sel
  with type env = JQuery.env) 
  (Env : TYP_ENV
   with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type binding = JQuery.binding
  with type env = JQuery.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
  (Desugar : Typedjs_desugar.DESUGAR
   with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type multiplicity = JQuery.multiplicity
  with type backformSel = JQuery.sel)
  : (JQUERY_TYP_ENV
     with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type sigma = JQuery.sigma
  with type multiplicity = JQuery.multiplicity
  with type binding = JQuery.binding
  with type structureEnv = Desugar.structureEnv
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
  type backformSel = JQuery.sel
  open Env
  open JQueryKinding
  module Css = JQuery.Css
  open Css_syntax

  module Strobe = JQuery.Strobe

  type structureEnv = Desugar.structureEnv

  let (senv : structureEnv ref) = ref Desugar.empty_structureEnv

  (* Consumes:
     env 
     t (typ)

     Produces t if t is of the form:
       TDom
       TId id -> TDom
       TUnion of TDoms (or TUnion of TDom, TUnion of Tdoms...)
     Otherwise, raises Typ_error *)
  let rec expose_tdoms (env : env) (t : typ) : typ =
    match unwrap_t t with
    | TDom _ -> t
    | _ -> begin match extract_t t with
      | Strobe.TUnion (s,t1,t2) -> 
        embed_t (Strobe.TUnion (s, (extract_t (expose_tdoms env (embed_t t1))), 
                                (extract_t (expose_tdoms env (embed_t t2)))))
      | Strobe.TId id -> expose_tdoms env (fst (lookup_typ_id id env))
      | _ ->  raise (* If it's anything else, then reject, and fail with a type error *)     
        (Strobe.Typ_error 
           (Pos.dummy,
            (Strobe.FixedString (sprintf "Malformed TDom: %s"(string_of_typ t)))))
    end


    (* Consumes: 
       env : env
       cm : clauseMap
       t : typ

       expose_tdoms t, then MSums the lookups for each TDom in t.
       Produces: the canonicalized  MSum *)
  let rec lookup_cm (env : env) (cm : Desugar.clauseMap) (t : typ) 
      : (typ * (typ -> multiplicity)) = 

    let open JQuery in

    (* Turns a typ or a TUnion of TUnions into a list of typs *)
    let rec to_list t = match (unwrap_t t) with
      | TStrobe (Strobe.TUnion (_,t1,t2)) ->
        (to_list (embed_t t1)) @ (to_list (embed_t t2))
      | _ -> [t] in

    (* Turns a list of TDoms into a multiplicity by summing the results
       the lookup of each TDom in the given cm *)
    let rec helper ts = match ts with 
      | [TDom (_,id,_,_)] -> IdMap.find id cm
      | (TDom (_,id,_,_))::rest ->
        MSum ((IdMap.find id cm), helper rest)
      | [] -> failwith "impossible: empty list"
      | _ -> failwith "JQuery_env: mult_of: found something other than a TDom in ts"; in
    
    let (s, mf) = extract_mult
      (canonical_multiplicity (helper (to_list (expose_tdoms env t)))) in

    match s with 
    | STyp t -> (t, (fun t -> mf (STyp t)))
    | _ -> failwith "JQuery_env: lookup_cm: failed to properly canonicalize return mult"

  (* end of lookup_cm *)

  let children (env : env ) (senv : structureEnv) (m : multiplicity)
      : multiplicity =
    let (_,cenv) = senv in
    let (s, mf) = extract_mult m in
    match s with 
    | STyp t ->
      let (t', mf') = (lookup_cm env cenv.Desugar.children t) in
      (mf (SMult (mf' t')))
    | SMult _ -> m (* Can't extract all the way, pass through *)
    
  let parent (env : env) (senv : structureEnv) (m : multiplicity) 
      : multiplicity = m

  let prev (env : env) (senv : structureEnv) (m : multiplicity)
      : multiplicity = m

  let next (env : env) (senv : structureEnv) (m : multiplicity)
      : multiplicity = m



    (* The terminating condition of transitive is:
       1. Two consecutive results of m<Element>, regardless of what m is. 
       2. Two consecutive results of the exact same multiplicity (including the type inside the multiplicity).

       Well-formedness checking should prevent any infinite loops, but this could use more testing.
    *)
  let rec transitive (env : env) (senv : structureEnv) (t : typ) (f : structureEnv -> typ -> multiplicity) : multiplicity =
    Strobe.traceMsg "In transitive, ";
    let open JQuery in
    let next = canonical_multiplicity (f senv t) in
    Strobe.traceMsg "next is: %s" (string_of_mult next);
    let recur () : multiplicity = 
      let (s, fs) = extract_mult next in
      begin
        match s with
        | STyp next_t ->
          if JQuery.equivalent_typ env t next_t then next else
          MSum (next, fs (SMult (transitive env senv next_t f)))
        | SMult m -> next
      end in
    match next with
    | MZero _
    | MSum (_, _)
    | MId _
    | _ -> if (t = TStrobe (Strobe.TId "Element")) || (t = TStrobe (Strobe.TTop))
      then begin match next with
      | MZeroPlus (MPlain (TStrobe (Strobe.TId "Element")))
      | MZeroPlus (MPlain (TStrobe Strobe.TTop))
      | MZeroOne (MPlain (TStrobe (Strobe.TId "Element")))
      | MZeroOne (MPlain (TStrobe Strobe.TTop))
      | MZero (MPlain (TStrobe (Strobe.TId "Element")))
      | MZero (MPlain (TStrobe Strobe.TTop))
      | MOnePlus (MPlain (TStrobe (Strobe.TId "Element")))
      | MOnePlus (MPlain (TStrobe Strobe.TTop))
      | MOne (MPlain (TStrobe (Strobe.TId "Element")))
      | MOne (MPlain (TStrobe Strobe.TTop)) -> next
      | _ -> recur ()
      end
      else recur ()

  let nextall (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    MOne (MPlain t)
    (* transitive env senv t nextsib *)

  let prevall (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    MOne (MPlain t)
    (* transitive env senv t prevsib *)

  let parents (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    MOne (MPlain t)
    (* transitive env senv t parent *)

  let find (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    MOne (MPlain t)
    (* transitive env senv t children *)

  (** Function: filterSel
      ==============================
      filterSel takes a type environment env, a backform environment benv, a type t, and a selector sel. It extracts the selector corresponding to its type argument, and intersects that selector with sel, resulting in inter. inter is then backformed into ids and both are wrapped in an MSum of TDoms. filterSel only deals with TDoms, TIds and TUnions. It should not encounter any other type.
  **)
  let rec filterSel (env : env) (benv : Desugar.backformEnv) (t : typ) (sel : string) : multiplicity = MOne (MPlain (TStrobe (Strobe.TTop)))
    (* Strobe.traceMsg "In filterSel "; *)
    (* let open JQuery in *)
    (* let s = Css.singleton sel in *)
    (* match t with *)
    (* | TDom (_,t,sels) -> *)
    (*   let inter = Css.intersect sels s in *)
    (*   let ids = backform benv inter in *)
    (*   Strobe.traceMsg "The intersection of %s with %s is %s, backformed into: " (Css.pretty sels) (Css.pretty s) (Css.pretty inter); *)
    (*   List.iter (fun id -> Strobe.traceMsg "%s" id) ids; *)
    (*   if ids == [] *)
    (*   then (MZero (MPlain (TDom (None, (TStrobe (Strobe.TId "Element")), inter)))) *)
    (*   else List.fold_left (fun acc id -> MSum (MOnePlus (MPlain (expose_tdoms env (TDom (None, (TStrobe (Strobe.TId id)), inter)))), acc)) (MZero (MPlain (TStrobe (Strobe.TTop)))) ids *)
    (* | TStrobe (Strobe.TUnion (x, t1, t2)) ->  *)
    (*   Strobe.traceMsg "filterSel called with TUnion %s with %s" (string_of_typ (embed_t t1)) (string_of_typ (embed_t t2)); *)
    (*   MSum (filterSel env benv (embed_t t1) sel, filterSel env benv (embed_t t2) sel) *)
    (* | TStrobe (Strobe.TId x) -> begin *)
    (*   Strobe.traceMsg "filterSel called with TId %s" x; *)
    (*   Strobe.traceMsg "%s is: %s in the environment" x (string_of_typ (fst (lookup_typ_id x env))); *)
    (*   try filterSel env benv (fst (lookup_typ_id x env)) sel with Not_found -> failwith ("error: unbound TId " ^ x) *)
    (*     end *)
    (* | _ -> Strobe.traceMsg "filterSel encountered a non-tdom, non-tunion type %s" (string_of_typ t); MZero (MPlain (TStrobe (Strobe.TTop))) *)

  let filterJQ (benv : Desugar.backformEnv) (typ : typ) : multiplicity =
    let open JQuery in
    MZero (MPlain (TStrobe (Strobe.TTop)))


  (* returns an MSum of TDoms *)
  let jQuery (env : env) (benv : Desugar.backformEnv) (sel : string) : multiplicity =
    MOne (MPlain (TStrobe Strobe.TTop))
    (* (\* check whether sel is legal in the context of given local structure *\) *)
    (* let env_specs = List.flatten (List.map Css.speclist (List.map snd2 benv)) in *)
    (* let sel_specs = Css.speclist (Css.singleton sel) in *)
    (* (\* sel_specs and env_specs should overlap, otherwise give a warning *\) *)
    (* let overlap = List.exists (fun s -> List.mem s env_specs) sel_specs in *)
    (* let open JQuery in *)
    (* let s = Css.singleton sel in *)
    (* let ids = backform benv s in *)
    (* let sum = List.fold_left (fun acc id -> MSum (MOnePlus (MPlain (expose_tdoms env (TDom (None, (TStrobe (Strobe.TId id)), s)))), acc)) (MZero (MPlain (TStrobe (Strobe.TTop)))) ids in *)
    (* match ids, overlap with *)
    (* | [], true -> MZero (MPlain (TDom (None, (TStrobe (Strobe.TId "Element")), s))) *)
    (* | [], false -> MZeroPlus (MPlain (TDom (None, (TStrobe (Strobe.TId "Element")), s))) *)
    (* | _, true -> sum *)
    (* | _, false -> *)
    (*   (\* adding element *\) *)
    (*   MSum (MZeroPlus (MPlain (TDom (None, (TStrobe (Strobe.TId "Element")), s))), sum) *)

  (**** End Local Structure ***)



  let print_structureEnv lbl (senv : structureEnv) = 
    let open FormatExt in
    let open Desugar in
    let (benv, cenv) = senv in
    let benv = List.fold_left (fun (acc : Css.t IdMap.t) elem -> IdMap.add (fst elem) (snd elem) acc) IdMap.empty benv in
    let print_id id= text id in
    let print_benv_key = text in
    let print_benv_val = Css.p_css in
    let print_cenv_key = print_id in
    let print_cenv_val = JQuery.Pretty.multiplicity in
    label lbl [text "";
               text "Backform Environment";
               (IdMapExt.p_map ""
                  empty print_benv_key print_benv_val benv);
               text "Clause Environment";
               (IdMapExt.p_map "Children Clause" 
                  empty print_cenv_key print_cenv_val cenv.children);
               (IdMapExt.p_map "Parent Clause" 
                  empty print_cenv_key print_cenv_val cenv.parent);
               (IdMapExt.p_map "Prev Sib Clause" 
                  empty print_cenv_key print_cenv_val cenv.prev);
               (IdMapExt.p_map "Next Sib Clause" 
                  empty print_cenv_key print_cenv_val cenv.next)]


  let print_env env fmt = 
    Env.print_env env fmt

  let parse_env_buf = Env.parse_env_buf
  let parse_env = Env.parse_env
  let parse_env_file = Env.parse_env_file
  let lookup_lbl = Env.lookup_lbl
  let clear_labels = Env.clear_labels

  let bind x b (env : env) : env = 
    let bs = try IdMap.find x env with Not_found -> [] in
    let bs = List.filter (fun b' -> match unwrap_b b', b with
      | BMultBound _, BMultBound _
      | BStrobe (Strobe.BTermTyp _), BStrobe (Strobe.BTermTyp _)
      | BStrobe (Strobe.BTypBound _), BStrobe (Strobe.BTypBound _)
      | BStrobe (Strobe.BTyvar _), BStrobe (Strobe.BTyvar _)
      | BStrobe (Strobe.BLabelTyp _), BStrobe (Strobe.BLabelTyp _) -> false
      | _ -> true) bs in
    IdMap.add x (b::bs) env
  let bind' x b (env : env) = bind x (JQuery.embed_b b) env
  let bind_id x t (env : env) = bind' x (Strobe.BTermTyp (JQuery.extract_t t)) env
  let bind_lbl x t env = bind' x (Strobe.BLabelTyp (JQuery.extract_t t)) env
  let raw_bind_typ_id x t k (env : env) = 
    match JQuery.embed_k k with 
    | JQuery.KMult _ -> raise (Strobe.Kind_error (Printf.sprintf "Trying to bind %s at type %s with kind %s" 
                                                    x (Strobe.string_of_typ t) (Strobe.string_of_kind k)))
    | _ -> bind' x (Strobe.BTypBound (t, k)) env
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


  (* Consumes an env and a list of declarations 
     1) Gathers all top level declComps, and desugars them.
     2) Updates senv with compiled structureEnv
     3) Add local structure bindings returned form desugar into the env
     4) Add all non-structure decls into the env *)
  let extend_global_env env lst = 
    let open Typedjs_writtyp.WritTyp in

    (* 1) Partition lst into local structure declarations and non-structure
       declarations *)
    let (structure_decls, non_structure_decls) = 
      List.partition (fun d -> match d with
      | Decl _ -> true | _ -> false) lst in

    (* First gather structure declarations and compile into structureEnv *)
    
    let top_level_declComps = List.map (fun d -> match d with
      | Decl (_,dc) -> dc | _ -> failwith "impossible") structure_decls in


    (* Compile bindings and structureEnv from local structure *)
    let (bindings, compiled_senv) = 
      let wfs = (Desugar.well_formed_structure top_level_declComps) in
      Desugar.desugar_structure wfs in
    (* Perform well-formedness test for local structure *)
    
    (* 2) Update senv *)
    senv := compiled_senv;


    (* 3) Add bindings compiled in desugar_structure to the env *)
    let env = IdMap.fold (fun id t new_env ->
      (try
         ignore (lookup_typ_id id new_env);
         raise (Not_wf_typ (sprintf "the type %s is already defined" id))
       with Not_found ->
         let k = kind_check new_env [] (STyp t) in
         raw_bind_typ_id id (extract_t (apply_name (Some id) t)) (extract_k k) new_env))
      bindings env in


    (* 4) Finally add all non-structure decls to the env *)

    let lst = non_structure_decls in
           
    let desugar_typ p t = JQuery.extract_t (Desugar.desugar_typ p t) in
    let rec add recIds env decl = match decl with
      | Decl (_, (name,_,_,_,_)) -> 
        failwith (sprintf "JQUERYextend_global_env: impossible: all local structure declarations should have already been compiled, but Decl %s was not." name)
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
           let t' = Desugar.desugar_typ p writ_typ in
           let t'' = JQuery.squash env t' in
           (* Printf.eprintf "Binding %s to %s\n" x (string_of_typ (apply_name (Some x) t)); *)
           let k = kind_check env recIds (STyp t'') in
           raw_bind_typ_id x (extract_t (apply_name (Some x) t'')) (extract_k k) env)
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
          | Decl _
          | EnvPrim _
          | RecBind _ -> []) binds) in
        (* Printf.eprintf "Recursively including ids: "; *)
        (* List.iter (fun x -> Printf.eprintf "%s " x) ids; *)
        List.fold_left (add ids) env binds
          
    in 
    
    List.fold_left (add []) env lst


  (* End of extend_global_env *)

  (* let rec resolve_special_functions env senv t =  *)
  (*   Strobe.traceMsg "Attempting to resolve: %s" (string_of_typ t); *)
  (*   resolve_special_functions' env senv t *)
  let rec resolve_special_functions (env : env) (senv : structureEnv) (t : typ) =
    let rec resolve_sigma s = match s with
      | STyp t -> STyp (rjq t)
      | SMult m -> SMult (resolve_mult m) 
    and resolve_mult m =
      let rm = resolve_mult in
      match m with
      | MPlain t -> MPlain (rjq t)
      | MId _ -> m
      | MZero m-> MZero (rm m)
      | MOne m -> MOne (rm m)
      | MZeroOne m -> MZeroOne (rm m)
      | MOnePlus m -> MOnePlus (rm m)
      | MZeroPlus m -> MZeroPlus (rm m)
      | MSum (m1, m2) -> MSum (rm m1, rm m2)
    and  rjq t = match t with
      | TForall (s,id,sigma,t) -> TForall(s,id,resolve_sigma sigma, t)
      | TLambda _ -> t
      | TApp (TStrobe (Strobe.TPrim "selector"), [STyp (TStrobe (Strobe.TRegex pat))]) ->
        Strobe.traceMsg "resolving selector primitive";
        begin match Strobe.Pat.singleton_string pat with
        | Some s -> 
          let m = canonical_multiplicity (jQuery env (fst senv) s) in
          Strobe.traceMsg "jQuery(%s) returns %s" s (string_of_mult m);
          TApp (TStrobe (Strobe.TId "jQ"), [(SMult m); STyp (TStrobe (Strobe.TId "AnyJQ"))])
        | None -> failwith "pattern cannot be converted to string??"
        end
      | TApp(TStrobe (Strobe.TPrim "childrenOf"), [STyp t]) ->
        failwith "childrenOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "parentOf"), [STyp t]) ->
        failwith "parentOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "prevSibOf"), [STyp t]) ->
        failwith "prevSibOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "nextSibOf"), [STyp t]) ->
        failwith "nextSibOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "findOf"), [STyp t]) ->
        failwith "findOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "parentsOf"), [STyp t]) ->
        failwith "parentAllOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "prevAllOf"), [STyp t]) ->
        failwith "prevAllOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "nextAllOf"), [STyp t]) ->
        failwith "nextAllOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "oneOf"), [STyp t]) ->
        failwith "oneOf at outermost level"
      | TApp(TStrobe (Strobe.TPrim "filterSel"), [STyp t]) ->
        failwith "filterSel at outermost level"
      | TApp(t, args) ->
        (* Strobe.traceMsg "rjq called with TApp : %s" (string_of_typ t); *)
        TApp(rjq t, List.map (fun s -> match s with
        | SMult m -> begin match extract_mult m with
          | (STyp (TApp ((TStrobe (Strobe.TPrim "filterSel")), [SMult m; STyp (TStrobe (Strobe.TRegex pat))])), m1) ->
            let (s, m2) = extract_mult m in
              begin match s with
                | STyp t -> 
                  SMult (canonical_multiplicity (m2 (SMult (m1 (SMult (filterSel env (fst senv) t (match Strobe.Pat.singleton_string pat with Some s -> s | None -> failwith "regex argument to @filterSel cannot be converted to string")))))))
                | SMult m -> s
              end
          | (STyp (TApp ((TStrobe (Strobe.TPrim "filterSel")), [SMult m; STyp (TStrobe (Strobe.TId _))])), _) -> s
          | (STyp (TApp ((TStrobe (Strobe.TPrim "filterSel")), l)), _) ->
            failwith "filterSel not called with a mult argument and a string"
          | (STyp (TApp ((TStrobe (Strobe.TPrim "oneOf")), [SMult m])), m1) ->
            let (s, _) = extract_mult m in SMult (
              begin 
                match s with
                | STyp t -> MOne (MPlain t)
                | SMult m -> (canonical_multiplicity (MOne m))
              end)
          | (STyp (TApp ((TStrobe (Strobe.TPrim "oneOf")), _)), _) ->
            failwith "oneOf not called with a single mult argument"
          | (STyp (TApp ((TStrobe (Strobe.TPrim "childrenOf")), [SMult m])), m1) ->
            SMult (canonical_multiplicity (m1 (SMult (children env senv (resolve_mult m)))))
          | (STyp (TApp ((TStrobe (Strobe.TPrim "childrenOf")), _)), _) ->
            failwith "childrenOf not called with a single mult argument"
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "parentOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t ->  *)
          (*     SMult (canonical_multiplicity  *)
          (*              (m1 (SMult (m2 (SMult (parent env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "parentOf")), _)), _) -> *)
          (*   failwith "parentOf not called with a single mult argument" *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "prevSibOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t ->  *)
          (*     SMult (canonical_multiplicity  *)
          (*              (m1 (SMult (m2 (SMult (prevsib env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "prevSibOf")), _)), _) -> *)
          (*   failwith "prevSibOf not called with a single mult argument" *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "nextSibOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t ->  *)
          (*     SMult (canonical_multiplicity  *)
          (*              (m1 (SMult (m2 (SMult (nextsib env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "nextSibOf")), _)), _) -> *)
          (*   failwith "nextSibOf not called with a single mult argument" *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "findOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t ->  *)
          (*     SMult (canonical_multiplicity (m1 (SMult (m2 (SMult (find env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "findOf")), _)), _) -> *)
          (*   failwith "findOf not called with a single mult argument" *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "parentsOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t -> SMult (canonical_multiplicity (m1 (SMult (m2 (SMult (parents env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "parentsOf")), _)), _) -> *)
          (*   failwith "parentsOf not called with a single mult argument" *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "prevAllOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t -> SMult (canonical_multiplicity (m1 (SMult (m2 (SMult (prevall env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "prevAllOf")), _)), _) -> *)
          (*   failwith "prevAllOf not called with a single mult argument" *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "nextAllOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t -> SMult (canonical_multiplicity (m1 (SMult (m2 (SMult (nextall env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "nextAllOf")), _)), _) -> *)
          (*   failwith "nextAllOf not called with a single mult argument" *)
          | _ -> s
        end
        | STyp t -> s
        ) args)
      | TDom (s,id, t, sel) -> TDom (s,id,rjq t, sel)
      | TStrobe t -> TStrobe (rs t)
    and rs t = 
      let rs_obj o = Strobe.mk_obj_typ 
        (List.map (third3 rs) (Strobe.fields o)) 
        (Strobe.absent_pat o) in
      match t with 
      | Strobe.TPrim s -> t
      | Strobe.TUnion (s,t1,t2) -> Strobe.TUnion(s, rs t1, rs t2)
      | Strobe.TInter (s,t1,t2) -> Strobe.TInter(s, rs t1, rs t2)
      | Strobe.TArrow (ts,t1,t2) ->
        Strobe.TArrow(List.map rs ts,
                      (opt_map rs t1),
                      rs t2)
      | Strobe.TThis t -> Strobe.TThis (rs t)
      | Strobe.TObject o -> Strobe.TObject (rs_obj o)
      | Strobe.TWith (t, o) -> Strobe.TWith (rs t, rs_obj o)
      | Strobe.TRegex _ -> t
      | Strobe.TRef (s, t) -> Strobe.TRef (s, rs t)
      | Strobe.TSource (s, t) -> Strobe.TSource (s, rs t)
      | Strobe.TSink (s, t) -> Strobe.TSink (s, rs t)
      | Strobe.TTop -> Strobe.TTop
      | Strobe.TBot -> Strobe.TBot
      | Strobe.TForall (s,id,t1,t2) -> Strobe.TForall(s,id,rs t1, t2)
      | Strobe.TId id -> t
      | Strobe.TRec _ -> t
      | Strobe.TLambda _ -> t
      | Strobe.TApp (t, ts) -> Strobe.TApp (rs t, (List.map rs ts))
      | Strobe.TFix _ -> t
      | Strobe.TUninit tor -> 
        tor := opt_map rs !tor;
        Strobe.TUninit tor
      | Strobe.TEmbed t -> Strobe.TEmbed (rjq t) in
    rjq t
      
end
  
