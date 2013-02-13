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
  (Desugar : Typedjs_desugar.JQUERY_DESUGAR
   with type typ = JQuery.typ
   with type writtyp = Typedjs_writtyp.WritTyp.t
  with type kind = JQuery.kind
  with type multiplicity = JQuery.multiplicity
  with type backformSel = JQuery.sel
  with type voidBackformSel = JQuery.sel)
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
  type voidbackformSel = JQuery.sel
  open Env
  open JQueryKinding
  module Css = JQuery.Css
  open Css_syntax

  module Strobe = JQuery.Strobe

  type structureEnv = Desugar.structureEnv

  let (senv : structureEnv ref) = ref Desugar.empty_structureEnv

  let use_strict_selections = ref false

  let do_use_strict_selections () = use_strict_selections := true

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
        embed_t (Strobe.TUnion
                   (s, (extract_t (expose_tdoms env (embed_t t1))),
                    (extract_t (expose_tdoms env (embed_t t2)))))
      | Strobe.TInter (s,t1,t2) ->
        embed_t (Strobe.TInter
                   (s, (extract_t (expose_tdoms env (embed_t t1))),
                    (extract_t (expose_tdoms env (embed_t t2)))))
      | Strobe.TId "Element" -> t
      | Strobe.TId id -> expose_tdoms env (fst (lookup_typ_alias id env))
      | t' ->  raise
        (Strobe.Typ_error
           (Pos.dummy,
            (Strobe.FixedString (sprintf "Malformed TDom: %s"(string_of_typ t)))))
    end

  (* Produces a multiplicity list *)
  let rec get_all_x_of (env : env) (cm : Desugar.clauseMap) (t : typ)
      : multiplicity list =

    let open JQuery in

    (* Turns a TDoms or a TUnion of TDoms into a list of mults *)
    let rec to_list t = match (unwrap_t t) with
      | TStrobe (Strobe.TUnion (_,t1,t2)) ->
        (to_list (embed_t t1)) @ (to_list (embed_t t2))
      | TDom (_,id,_,_) -> [IdMap.find id cm]
      | TStrobe (Strobe.TId "Element") -> [IdMap.find "Element" cm]
      | _ -> failwith "JQuery_env: get_all_x_of: encountered something other than a TDom"
    in

    to_list (expose_tdoms env t)


  (* MSum every mult in ms and canonicalize *)
  let msum_ms (ms : multiplicity list) : multiplicity =
    canonical_multiplicity
      (List.fold_left (fun macc m -> MSum (macc,m))
         (MZero (MPlain (embed_t Strobe.TBot))) ms)


  let munion_ms (ms : multiplicity list) : multiplicity =
    let (mmin, mmax) = List.fold_left (fun (mmin, mmax) m -> match m with
      | MZero _ -> (min mmin 0, max mmax 0)
      | MOne _ -> (min mmin 1, max mmax 1)
      | MPlain _ -> (min mmin 1, max mmax 1)
      | MOnePlus _ -> (min mmin 1, max mmax 2)
      | MZeroOne _ -> (min mmin 0, max mmax 1)
      | MZeroPlus _ -> (min mmin 0, max mmax 2)
      | MSum _ -> failwith "Got MSum where we didn't expect any"
      | MId _ -> failwith "Got MId where we didn't expect any") (2, 0) ms in
    let make t = match (mmin, mmax) with
      | 0, 0 -> MZero (MPlain t)
      | 1, 1 -> MOne (MPlain t)
      | 0, 1 -> MZeroOne (MPlain t)
      | 1, 2 -> MOnePlus (MPlain t)
      | 0, 2 -> MZeroPlus (MPlain t)
      | _ -> failwith (Printf.sprintf "Weird min/max combo: (%d, %d)" mmin mmax) in
    let ts = List.map (fun m -> match extract_mult m with
      | STyp t, _ -> t
      | SMult _, _ -> failwith (Printf.sprintf "Found a multiplicity with no type: %s" (string_of_mult m))) ms in
    let union = List.fold_left (fun t1 t2 ->
      if t1 = Strobe.TBot then extract_t t2 else Strobe.TUnion(None, t1, extract_t t2))
      Strobe.TBot ts in
    canonical_multiplicity (make (embed_t union))

  let children (env : env ) (senv : structureEnv) (t : typ) : multiplicity =
    let cenv = (snd senv) in
    msum_ms (get_all_x_of env cenv.Desugar.children t)

  let parent (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    let cenv = (snd senv) in
    munion_ms (get_all_x_of env cenv.Desugar.parent t)

  let prev (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    let cenv = (snd senv) in
    munion_ms (get_all_x_of env cenv.Desugar.prev t)

  let next (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    let cenv = (snd senv) in
    munion_ms (get_all_x_of env cenv.Desugar.next t)


  let rec extract_sum m = match m with
    | MSum (m1, m2) -> extract_sum m1 @ extract_sum m2
    | _ -> [m]

  let transitive (op : env -> structureEnv -> typ -> multiplicity)
      (included : env -> multiplicity -> multiplicity -> bool)
      (env : env) (senv : structureEnv) (t : typ) : multiplicity =
    let rec helper (acc : multiplicity list) (m : multiplicity) : multiplicity =
      helper' acc m
    (* Strobe.trace "transitive_helper"  *)
    (*   (Printf.sprintf "acc = [%s], m = %s" (String.concat ", " (List.map string_of_mult acc)) (string_of_mult m)) *)
    (*   (fun _ -> true) (fun () -> helper' acc m) *)
    and helper' acc m =
      match m with
      | MZero _ -> msum_ms acc
      | _ ->
        let res = match extract_mult (canonical_multiplicity m) with
          | STyp t, m' ->
            let res_op = op env senv t in
            let res = canonical_multiplicity (m' (SMult res_op)) in
            res
          | SMult (MSum _ as sum), _ -> begin
            let sum_pieces = extract_sum sum in
            let oper_pieces = List.map (fun p ->
              let (s, m) = extract_mult p in
              match s with
              | STyp t -> m (SMult (op env senv t))
              | SMult m -> m) sum_pieces in
            let combined = msum_ms oper_pieces in
            canonical_multiplicity combined
          end
          | SMult _, _ -> failwith "Got unexpected multiplicity in transitive"
        in
        if List.mem res acc
        then msum_ms acc
        else helper (res::acc) res
    in
    let first = op env senv t in
    helper [first] first
    (* Strobe.trace "transitive" (Printf.sprintf "t = %s" (string_of_typ t)) (fun _ -> true) *)
    (*   (fun () -> *)
    (*     let first = op env senv t in *)
    (*     helper [first] first) *)



  let find included env senv t = transitive children included env senv t
  let nextAll included env senv t = transitive next included env senv t
  let prevAll included env senv t = transitive prev included env senv t
  let parentsAll included env senv t = transitive parent included env senv t


  let rec filterSel (env : env) (benv : Desugar.backformEnv) 
      (fm : multiplicity) (sel_str : string) : multiplicity =

    let filter_sel = Css.singleton sel_str in

    let is_known_id = 
      (not (Css.is_empty filter_sel)) && (* selector isn't trivially empty *)
      Css.is_empty (Css.intersect filter_sel (Css.sel_from_id "#_THIS_IS_NOT_AN_ID_#")) && (* selector has an ID *)
      1 = List.length (List.filter (fun (_, s, _) -> not (Css.is_empty (Css.intersect filter_sel s))) benv) in

    let strip_element m =
      if not is_known_id then m else
      let rec collect_parts m = match m with
        | MSum (m1, m2) -> collect_parts m1 @ collect_parts m2
        | _ -> [m] in
      let m_parts = collect_parts m in
      match List.filter (fun m -> match canonical_multiplicity m with
      | MZero (MPlain (TStrobe (Strobe.TId "Element")))
      | MOne (MPlain (TStrobe (Strobe.TId "Element")))
      | MZeroOne (MPlain (TStrobe (Strobe.TId "Element")))
      | MOnePlus (MPlain (TStrobe (Strobe.TId "Element")))
      | MZeroPlus (MPlain (TStrobe (Strobe.TId "Element"))) -> false
      | m' -> true) m_parts with
      | [] -> m
      | m'::m_parts' -> List.fold_left (fun acc m -> MSum (acc, m)) m' m_parts' in

    let rec filter_m m = 
      begin match canonical_multiplicity m with 
      | MZero (MPlain t) -> m
      | MOne (MPlain t) -> MOne (filter_t t)
      | MZeroOne (MPlain t) -> MZeroOne (filter_t t)
      | MOnePlus (MPlain t) -> MOnePlus (filter_t t)
      | MZeroPlus (MPlain t) -> MZeroPlus (filter_t t)
      | MSum (m1,m2) -> MSum ((filter_m m1), (filter_m m2))
      | MId _ -> failwith "JQuery_env: filterSel: can't handle MIds here"
      | MPlain _ -> failwith 
        "JQUery_env: filterSel: should never encounter MPlain here"
      | _ -> failwith "JQuery_env: filterSel: mult not in canonical form"
      end

    and filter_t (t : typ) : multiplicity  = 
      
      (* Strobe.traceMsg "filterSel: filtering type %s" (string_of_typ t); *)

      let rec helper t = 

        let filter_tdom t = match t with
          | TDom (s,name,node_typ,sel) -> 
            let inter = Css.intersect sel filter_sel in
            if Css.is_empty inter then None
            else Some (TDom (s,name,node_typ,inter))

          | TStrobe (Strobe.TSource (Some "Element", Strobe.TObject _)) -> 
            (* This is a bit of a hack, because things have already been exposed.  But it's safe,
               given how we've defined Element, and how we use it in our code *)
            Some (TStrobe (Strobe.TId "Element"))
          | _ -> 
            (* Strobe.traceMsg "filtering type %s" (string_of_typ t); *)
            failwith "JQuery_env:filterSel: can only filter tdoms" in
        
        match t with
        | TDom _ -> filter_tdom t
        | _ -> begin match (extract_t t) with 
          | Strobe.TUnion (s,t1,t2)->
            (* Elim things that did not match *)
            begin match (helper (embed_t t1)),(helper (embed_t t2)) with
            | Some t1, Some t2 -> 
              Some (embed_t (Strobe.TUnion (s,(extract_t t1),(extract_t t2))))
            | Some t,_
            | _,Some t -> Some t
            | None, None -> None
            end
          | Strobe.TId id -> filter_tdom (fst (lookup_typ_id id env))
          | _ -> failwith
            "JQuery_env: filterSel: Can only handle TUnions and TIds, and TDoms"
        end in
        

      match helper t with 
      | Some t -> MOne (MPlain t)
      | None -> MZero (MPlain (embed_t (Strobe.TId "Element"))) in
    (* END filter_t *)

      canonical_multiplicity (strip_element (filter_m fm))
  (* END filterSel *)

    

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
    MZero (MPlain (TStrobe (Strobe.TBot)))


  let jQuery_fn (env : env)
      (included: env -> multiplicity -> multiplicity -> bool)
      (select_str : string) : multiplicity =

    let open Css_syntax in

    let senv = !senv in 
    let (benv,_) = senv in

    let select_sel = Css.singleton select_str in

    (* Convert sel to list of regsels. This should be a singleton list *)
    let select_rs = match Css.sel2regsels select_sel with
      | [rs] -> rs
      | _ -> failwith "JQuery_env: jQuery: should have gotten just one regsel from sel" in

    (* Convert sels to regsels in benv *)
    let structure_rss = List.map (fun (id, sel, vsel) ->
      (id, (Css.sel2regsels sel), (Css.sel2regsels vsel))) benv in


    (* Collect set of all specs that appear in benv *)
    
    let isolated_specs = List.fold_left (fun spec_set (id, sels,_) ->
      List.fold_left (fun spec_set rs ->
        List.fold_left (fun spec_set (_,(_,sel_specs)) ->
          List.fold_left (fun spec_set spec -> match spec with
            (* Treat special classes as normal classes for comparison ease later *)
            | SpSpecClass (s,_) -> SpecSet.add (SpClass s) spec_set
            | _ -> SpecSet.add spec spec_set)
            spec_set sel_specs)
          spec_set rs)
        spec_set sels)
      SpecSet.empty structure_rss in


    (* Helper: Does given spec list contains isolated (local structure) spec? *)
    let is_isolated ss = List.exists (fun s -> SpecSet.mem s isolated_specs) ss in

    (* Partition select_rs into two regsels. Prefix includes everything down
       to the first simple that includes an isolated spec. Suffix is the rest
       of the regsel after (and not including) that simple. Isolated bool
       indicates whether or not an isolated spec was found*)
    let (prefix,suffix,isolated) = 
      let rec split pre suf = match suf with 
        | [] -> (List.rev pre),[],false
        (* | [] -> failwith "JQuery_env: jQuery_fn: should have already terminated" *)
        (* | [(_, (_,specs))] ->  *)
        (*   let suf = if (is_isolated specs) then suf else [] in (pre, suf) *)
        | ((_, (_,specs)) as hd)::tl -> 
          let pre = hd::pre in
          if (is_isolated specs) then (List.rev pre), tl, true
          else split pre tl in
      split [] select_rs in


    if (!use_strict_selections && (not isolated)) then
      MZero (MPlain (embed_t (Strobe.TId "Element")))
    else (* if isolated spec was found  *) begin
      
      let prefix_sel = Css.regsel2sel prefix in

      (* All ids in benv matching the prefix *)
      let prefix_matches = 
        List.fold_left (fun matches (id,_,vsel) -> 
          if (Css.is_overlapped prefix_sel vsel) then id::matches
          else matches)
          [] benv in

      (* Helper: Given a combinator and an list of ids representing pieces
         of local structure, get the 'next' ids based on the relationship
         defined by the combinator *)
      let get_next (c : combinator) (ids : id list) : id list = 

        (* Helper *)
        let rec unwrap_msum m =

          let rec unwrap_t t =  match t with 
            | Strobe.TId id -> [id]
            | Strobe.TUnion (_,t1,t2) -> List.append (unwrap_t t1) (unwrap_t t2)
            | _ -> failwith (sprintf "JQuery_env: jQuery_fn: got something other than a tid or a tunion in clausemaps: %s"(Strobe.string_of_typ t)) in

          match m with

          | MSum (m1,m2) -> List.append (unwrap_msum m1) (unwrap_msum m2)
          | MZero _ -> []
          (* Stop if it's nothing and don't try to extract the type *)
          | _ -> begin match (fst (extract_mult m)) with 
            | STyp t -> unwrap_t (extract_t t)
            | _ -> failwith 
              "JQuery_env: jQuery_fn: got mult after extract_mult" end 
        in


        List.flatten (List.map (fun id -> 
          let make_tid id = embed_t ( Strobe.TId id) in 
          let sm = simplify_msum in match c with 
        | Desc -> unwrap_msum (sm (find included env senv (make_tid id)))
        | Kid -> unwrap_msum (sm (children env senv (make_tid id)))
        | Sib -> unwrap_msum (sm (nextAll included env senv (make_tid id)))
        | Adj -> unwrap_msum (sm (next env senv (make_tid id)))) ids) in
      (* END get_next *)


      (* continue matching with the suffix *)
      let rec get_matches ids match_rs suf = match suf with 
        | [] -> ids
        | ((comb,_) as suf_hd)::suf_tl -> 
          let new_match_rs = List.append match_rs [suf_hd] in
          let next_ids = 
            List.filter (fun id -> 
              let ssel = (Css.regsel2sel new_match_rs) in
              let vsel = (thd3 (List.find (fun (id2,_,_) -> id2 = id) benv)) in
              let res = Css.is_overlapped ssel vsel in
              (* let resStr = if res then "does" else "does NOT" in *)
              (* Printf.eprintf "%s %s %s" *)
              (*   (FormatExt.to_string Css.p_css ssel) *)
              (*   resStr *)
              (*   (FormatExt.to_string Css.p_css vsel); *)
              res) (get_next comb ids) in
          get_matches next_ids new_match_rs suf_tl in
      (* END get_matches *)

      (* Helper: intersect select_sel with the sel of a given id *)
      let get_inter id = 
        let sel = (snd3 (List.find (fun (id2,_,_) -> id = id2) benv)) in
        Css.intersect sel select_sel in
                  

      (* Helper: Given an id, lookups up the current TDom associated with id
         and returns a one plus of that tdom with an updated sel *)
      let optd id sel =  
        let cur_tdom = fst (lookup_typ_alias id env) in
        match cur_tdom with 
        | TDom(s,_,nt,_) -> MOnePlus (MPlain (TDom (s,id,nt,sel)))
        | _ -> failwith 
          (sprintf "JQuery_env: jQuery_fn: impossible, %s is not a TDom"id) in

      (* Finally, build multiplicity from matches and return *)
      match get_matches prefix_matches prefix suffix with
      | [] -> MZero (MPlain (embed_t (Strobe.TId "Element")))
      | [id] -> optd id (get_inter id)
      | ids -> msum_ms (List.map (fun id -> optd id (get_inter id)) ids)
        
            
    end


  (*** END jQuery_fn ***)


  (*** END Local Structure ***)

  let print_structureEnv lbl (senv : structureEnv) =
    let open FormatExt in
    let open Desugar in
    let (benv, cenv) = senv in
    let print_benv = horzOrVert (List.map (fun (id,sel,vsel) ->
      horz [text id; Css.p_css sel; Css.p_css vsel]) benv) in
    let print_id id= text id in
    let print_cenv_key = print_id in
    let print_cenv_val = JQuery.Pretty.multiplicity in
    label lbl [text "";
               text "Backform Environment";
               print_benv;
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
      | BStrobe (Strobe.BTypDef _), BStrobe (Strobe.BTypDef _)
      | BStrobe (Strobe.BTypBound _), BStrobe (Strobe.BTypBound _)
      | BStrobe (Strobe.BTyvar _), BStrobe (Strobe.BTyvar _)
      | BStrobe (Strobe.BLabelTyp _), BStrobe (Strobe.BLabelTyp _) -> false
      | _ -> true) bs in
    IdMap.add x (b::bs) env
  let bind' x b (env : env) = bind x (JQuery.embed_b b) env
  let bind_id x t (env : env) = bind' x (Strobe.BTermTyp (JQuery.extract_t t)) env
  let bind_lbl x t env = bind' x (Strobe.BLabelTyp (JQuery.extract_t t)) env

  let bind_typdef x t k env =
    match JQuery.embed_k k with
    | JQuery.KMult _ -> raise (Strobe.Kind_error (Printf.sprintf "Trying to bind typedef %s : %s with kind %s"
                                                    x (Strobe.string_of_typ t) (Strobe.string_of_kind k)))
    | _ -> bind' x (Strobe.BTypDef (t, k)) env
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
  let lookup_typ_alias x env = Env.lookup_typ_alias x env

  let lookup_mult_id x (env : env) =
    let bs = IdMap.find x env in
    match (ListExt.filter_map (fun b -> match (embed_b (extract_b b)) with
    | BMultBound (m,_) -> Some m
    | _ -> None) bs) with
    | [m] -> m
    | _ -> ((* Printf.eprintf "Couldn't find %s in lookup_mult_id\n" x; *) raise Not_found)

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
         ignore (lookup_typ_alias id new_env);
         raise (Not_wf_typ (sprintf "the type %s is already defined" id))
       with Not_found ->
         let k = kind_check new_env [] (STyp t) in
         bind_typdef id (extract_t (apply_name (Some id) t)) (extract_k k) new_env))
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
           ignore (lookup_typ_alias x env);
           raise (Not_wf_typ (sprintf "the type %s is already defined" x))
         with Not_found ->
           let t' = Desugar.desugar_typ p writ_typ in
           let t'' = JQuery.squash env t' in
           (* Printf.eprintf "Binding %s to %s\n" x (string_of_typ (apply_name (Some x) t)); *)
           let k = kind_check env recIds (STyp t'') in
           bind_typdef x (extract_t (apply_name (Some x) t'')) (extract_k k) env)
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

    in

    List.fold_left (add []) env lst


  (* End of extend_global_env *)

  let rec resolve_special_functions env senv included t =
    (* Strobe.traceMsg "Attempting to resolve: %s" (string_of_typ t); *)
      (* let rec resolve_special_functions (env : env) (senv : structureEnv) *)
      (*     (included : env -> multiplicity -> multiplicity -> bool) (t : typ) = *)
      resolve_special_functions' env senv included t
      (* (fun () -> resolve_special_functions' env senv included t) *)
  and resolve_special_functions' env senv included t =
    let rec resolve_sigma s = match s with
      | STyp t -> STyp (rjq t)
      | SMult m -> SMult (resolve_mult m)
    (* resolve_mult resolves special functions at top level. This is a hack and should be streamlined. *)
    and resolve_mult m =
      let rm = resolve_mult in
      match m with
      | MPlain t -> begin match t with
        | (TApp ((TStrobe (Strobe.TPrim ("childrenOf" as oper))), [SMult m]))
        | (TApp ((TStrobe (Strobe.TPrim ("nextSibOf" as oper))), [SMult m]))
        | (TApp ((TStrobe (Strobe.TPrim ("prevSibOf" as oper))), [SMult m]))
        | (TApp ((TStrobe (Strobe.TPrim ("parentOf" as oper))), [SMult m]))
        | (TApp ((TStrobe (Strobe.TPrim ("parentsOf" as oper))), [SMult m]))
        | (TApp ((TStrobe (Strobe.TPrim ("findOf" as oper))), [SMult m]))
        | (TApp ((TStrobe (Strobe.TPrim ("nextAllOf" as oper))), [SMult m]))
        | (TApp ((TStrobe (Strobe.TPrim ("prevAllOf" as oper))), [SMult m]))
          ->
          (* Strobe.traceMsg "resolving something other than filterSel"; *)
            let op = match oper with
              | "childrenOf" -> children
              | "nextSibOf" -> next
              | "prevSibOf" -> prev
              | "parentOf" -> parent
              | "findOf" -> find included
              | "nextAllOf" -> nextAll included
              | "prevAllOf" -> prevAll included
              | "parentsOf" -> parentsAll included
              | _ -> failwith "impossible: we only matched known strings" in
            let (s', m2) = extract_mult m in  
            begin match s' with
            | STyp t -> (canonical_multiplicity (m2 (SMult (op env senv (rjq t)))))
            | SMult (MSum _ as sum) -> begin
              let sum_pieces = extract_sum sum in
              let oper_pieces = List.map (fun p ->
                let (s, m) = extract_mult p in
                match s with
                | STyp t -> m (SMult (op env senv (rjq t)))
                | SMult m -> m) sum_pieces in
              let combined = msum_ms oper_pieces in
              (canonical_multiplicity combined)
            end
            | SMult _ -> m
            (* Could not extract down to a type. Return ORIGINAL sigma *)
            end
        | (TApp ((TStrobe (Strobe.TPrim ("childrenOf" as oper))), _))
        | (TApp ((TStrobe (Strobe.TPrim ("nextSibOf" as oper))), _))
        | (TApp ((TStrobe (Strobe.TPrim ("prevSibOf" as oper))), _))
        | (TApp ((TStrobe (Strobe.TPrim ("parentOf" as oper))), _))
        | (TApp ((TStrobe (Strobe.TPrim ("findOf" as oper))), _))
        | (TApp ((TStrobe (Strobe.TPrim ("nextAllOf" as oper))), _))
        | (TApp ((TStrobe (Strobe.TPrim ("prevAllOf" as oper))), _))
        | (TApp ((TStrobe (Strobe.TPrim ("parentsOf" as oper))), _))
          ->
          failwith (oper ^ " not called with a single mult argument")
        (*   | (STyp (TApp ((TStrobe (Strobe.TPrim "oneOf")), [SMult m])), m1) -> *)
        (*     let (s, _) = extract_mult m in SMult ( *)
        (*       begin  *)
        (*         match s with *)
        (*         | STyp t -> MOne (MPlain t) *)
        (*         | SMult m -> (canonical_multiplicity (MOne m)) *)
        (*       end) *)
        (*   | (STyp (TApp ((TStrobe (Strobe.TPrim "oneOf")), _)), _) -> *)
        (*     failwith "oneOf not called with a single mult argument" *)
        (* | (STyp (TApp ((TStrobe (Strobe.TPrim "parentOf")), [SMult m])), m1) -> *)
        (*   let (s, m2) = extract_mult m in *)
        (*   begin match s with *)
        (*   | STyp t ->  *)
        (*     SMult (canonical_multiplicity  *)
        (*              (m1 (SMult (m2 (SMult (parent env senv (rjq t))))))) *)
        (*   | SMult _ -> s *)
        (*   end *)
        | _ -> m (* Any other pattern, return original sigma *)
      end
      (* Strobe.traceMsg "calling rjq from resolve_mult on type %s" (string_of_typ t); *)
      (* Strobe.traceMsg "resolved type is: %s" (string_of_typ resolved); *)
      (* MPlain resolved *)
      | MId _ -> m
      | MZero m-> MZero (rm m)
      | MOne m -> MOne (rm m)
      | MZeroOne m -> MZeroOne (rm m)
      | MOnePlus m -> MOnePlus (rm m)
      | MZeroPlus m -> MZeroPlus (rm m)
      | MSum (m1, m2) -> MSum (rm m1, rm m2)
    (* and rt t = match t with *)
    (*   | TForall (s, id, sigma, t) -> TForall(s, id, resolve_sigma sigma, t) *)
    (*   | TLambda _ -> t *)
    (*   | TDom (s,id, t, sel) -> TDom (s,id,rt t, sel) *)
    (*   | TStrobe t -> TStrobe (rs t) *)
    and  rjq t = 
      (* begin match t with *)
      (* | TForall _ -> Strobe.traceMsg "rjq: encountered TForall %s" (string_of_typ t) *)
      (* | TLambda _ -> Strobe.traceMsg "rjq: encountered TLambda %s" (string_of_typ t) *)
      (* | TApp _ -> Strobe.traceMsg "rjq: encountered TApp %s" (string_of_typ t) *)
      (* | TDom _ -> Strobe.traceMsg "rjq: encountered TDom %s" (string_of_typ t) *)
      (* | TStrobe _ -> Strobe.traceMsg "rjq: encountered TStrobe %s" (string_of_typ t) *)
      (* end; *)
      match t with
      | TForall (s,id,sigma,t) -> TForall(s,id,resolve_sigma sigma, t)
      | TLambda _ -> t
      | TApp (TStrobe (Strobe.TPrim "selector"), [STyp (TStrobe (Strobe.TRegex pat))]) ->
        begin match Strobe.Pat.singleton_string pat with
        | Some s ->
          let m = (jQuery_fn env included s) in
          TApp (TStrobe (Strobe.TId "jQ"), [(SMult m); STyp (TStrobe (Strobe.TId "AnyJQ"))])
        | None -> failwith "pattern cannot be converted to string??"
        end
      | TApp (TStrobe (Strobe.TPrim "selector"), _) ->
        failwith "selector not called with a single pattern argument"
      | TApp(TStrobe (Strobe.TPrim ("childrenOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("parentOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("prevSibOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("nextSibOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("findOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("parentsOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("prevAllOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("nextAllOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("oneOf" as oper)), [STyp t])
      | TApp(TStrobe (Strobe.TPrim ("filterSel" as oper)), [STyp t]) ->
        failwith (oper ^ " at outermost level")
      | TApp(t, args) ->
        TApp(rjq t, List.map (fun s -> match s with
        | SMult m -> 
          (* Strobe.traceMsg "resolving multiplicity %s" (string_of_mult m); *)
          begin match extract_mult (canonical_multiplicity m) with
          | (STyp (TApp ((TStrobe (Strobe.TPrim "filterSel")), [SMult m; s])), m1) ->
            (* Strobe.traceMsg "resolving filterSel"; *)
            begin match s with
            | STyp (TStrobe (Strobe.TRegex pat)) ->
              let select_str = begin match Strobe.Pat.singleton_string pat with 
                | Some s -> s 
                | None -> failwith 
                  "regex argument to @filterSel cannot be converted to string" end in
              let resolved_m = (canonical_multiplicity (resolve_mult m)) in
              (* Strobe.traceMsg "resolving filterSel, inner type is %s" (string_of_mult resolved_m); *)
              (* Filter operates on a mult *)
              SMult (filterSel env (fst senv) resolved_m select_str)
            | STyp (TStrobe (Strobe.TId id)) -> s
            | _ ->
              failwith "filterSel called with a mult but not a string";
            end
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("childrenOf" as oper))), [SMult m])))), m1
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("nextSibOf" as oper))), [SMult m])))), m1
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("prevSibOf" as oper))), [SMult m])))), m1
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("parentOf" as oper))), [SMult m])))), m1
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("parentsOf" as oper))), [SMult m])))), m1
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("findOf" as oper))), [SMult m])))), m1
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("nextAllOf" as oper))), [SMult m])))), m1
          | ((STyp (TApp ((TStrobe (Strobe.TPrim ("prevAllOf" as oper))), [SMult m])))), m1
            ->
            (* Strobe.traceMsg "resolving something other than filterSel"; *)
              let op = match oper with
                | "childrenOf" -> children
                | "nextSibOf" -> next
                | "prevSibOf" -> prev
                | "parentOf" -> parent
                | "findOf" -> find included
                | "nextAllOf" -> nextAll included
                | "prevAllOf" -> prevAll included
                | "parentsOf" -> parentsAll included
                | _ -> failwith "impossible: we only matched known strings" in
              let (s', m2) = extract_mult m in begin match s' with
                | STyp t -> SMult
                  (canonical_multiplicity
                     (m1 (SMult (m2 (SMult (op env senv (rjq t)))))))
                | SMult (MSum _ as sum) -> begin
                  let sum_pieces = extract_sum sum in
                  let oper_pieces = List.map (fun p ->
                    let (s, m) = extract_mult p in
                    match s with
                    | STyp t -> m (SMult (op env senv (rjq t)))
                    | SMult m -> m) sum_pieces in
                  let combined = msum_ms oper_pieces in
                  SMult (canonical_multiplicity (m1 (SMult combined)))
                end
                | SMult _ -> s
              (* Could not extract down to a type. Return ORIGINAL sigma *)
              end
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("childrenOf" as oper))), _)), _)
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("nextSibOf" as oper))), _)), _)
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("prevSibOf" as oper))), _)), _)
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("parentOf" as oper))), _)), _)
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("findOf" as oper))), _)), _)
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("nextAllOf" as oper))), _)), _)
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("prevAllOf" as oper))), _)), _)
          | (STyp (TApp ((TStrobe (Strobe.TPrim ("parentsOf" as oper))), _)), _)
            ->
            failwith (oper ^ " not called with a single mult argument")
          (*   | (STyp (TApp ((TStrobe (Strobe.TPrim "oneOf")), [SMult m])), m1) -> *)
          (*     let (s, _) = extract_mult m in SMult ( *)
          (*       begin  *)
          (*         match s with *)
          (*         | STyp t -> MOne (MPlain t) *)
          (*         | SMult m -> (canonical_multiplicity (MOne m)) *)
          (*       end) *)
          (*   | (STyp (TApp ((TStrobe (Strobe.TPrim "oneOf")), _)), _) -> *)
          (*     failwith "oneOf not called with a single mult argument" *)
          (* | (STyp (TApp ((TStrobe (Strobe.TPrim "parentOf")), [SMult m])), m1) -> *)
          (*   let (s, m2) = extract_mult m in *)
          (*   begin match s with *)
          (*   | STyp t ->  *)
          (*     SMult (canonical_multiplicity  *)
          (*              (m1 (SMult (m2 (SMult (parent env senv (rjq t))))))) *)
          (*   | SMult _ -> s *)
          (*   end *)
          | _ -> s (* Any other pattern, return original sigma *)
        end
        (* Can't handle STyps here, return original sigma *)
        | STyp _ -> s) args)
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
