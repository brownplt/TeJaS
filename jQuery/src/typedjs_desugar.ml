open Prelude

module W = Typedjs_writtyp.WritTyp
module List = ListExt
module Pat = JQuery_syntax.Pat
module StringMap = Map.Make (String)
module StringMapExt = MapExt.Make (String) (StringMap)

module type DESUGAR = sig
  type typ
  type kind
  type multiplicity
  type backformSel
  type clauseMap = multiplicity IdMap.t

  (* TODO(liam) turn this into a set *)
  type backformEnv = (id * backformSel) list

  type clauseEnv = { children : clauseMap; 
                     parent : clauseMap; 
                     prev : clauseMap;
                     next : clauseMap }
  type structureEnv = (backformEnv * clauseEnv)
  exception Typ_stx_error of string
  val benv_eq : backformEnv -> backformEnv -> bool
  val desugar_typ : Pos.t -> W.t -> typ
  val well_formed_structure : W.declComp list -> W.declComp list
  val desugar_structure : W.declComp list -> (typ IdMap.t * structureEnv) 
  val empty_structureEnv : structureEnv
  exception Local_structure_error of string
end

module Make
  (S : Strobe_sigs.STROBE_TYPS with type pat = Pat.t)
  (JQ : JQuery_sigs.JQUERY_MODULE
   with type baseTyp = S.typ
  with type baseKind = S.kind
  with type typ = S.extTyp
  with type kind = S.extKind)
  : (DESUGAR 
     with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type backformSel = JQ.sel) =
struct
  type typ = JQ.typ
  type kind = JQ.kind
  type multiplicity = JQ.multiplicity
  module Css = JQ.Css
  type backformSel = JQ.sel

  exception Typ_stx_error of string

  (* Local Structure types *)
  type preClauseMap = id option list IdMap.t
  type clauseMap = multiplicity IdMap.t

  type backformEnv = (id * Css.t) list

  type clauseEnv = { children : clauseMap; 
                     parent : clauseMap; 
                     prev : clauseMap;
                     next : clauseMap }
  type preClauseEnv = { pce_children:  preClauseMap;
                        pce_parent: preClauseMap;
                        pce_prev: preClauseMap;
                        pce_next: preClauseMap }

  type preStructureEnv = backformEnv * preClauseEnv

  type structureEnv = backformEnv * clauseEnv  (* Exposed *)

  exception Local_structure_error of string

  (* END Local Structure types *)

  let benv_eq (env1 : backformEnv)  (env2 : backformEnv) = 
    let s1 = List.sort (fun e1 e2 -> compare (fst e1) (fst e2)) env1 in
    let s2 = List.sort (fun e1 e2 -> compare (fst e1) (fst e2)) env2 in
    List.for_all2 (fun e1 e2 -> Css.is_equal (snd e1) (snd e2)) s1 s2
  
  let error msg = 
    raise (Typ_stx_error msg)

  let is_star f = match f with
    | W.Star _ -> true
    | _ -> false

  let is_skull f = match f with
    | W.Skull _ -> true
    | _ -> false

  let is_absent f = match f with
    | W.Absent p -> true
    | _ -> false

  let pat_of f = match f with
    | W.Present (p, _) -> p
    | W.Inherited (p, _) -> p
    | W.Maybe (p, _) -> p
    | W.Absent p -> p
    | W.Skull p -> p
    | W.Star _ -> failwith "pat_of applied to Star _"

  let assert_overlap pat1 pat2 = match Pat.example (Pat.intersect pat1 pat2) with
    | None -> ()
    | Some str ->
      error (sprintf "%s and %s are overlapped. E.g.,\n%s\n is in both patterns." 
               (Pat.pretty pat1) (Pat.pretty pat2) str)

  let rec typ (writ_typ : W.t) : JQ.typ =
    JQ.embed_t (match writ_typ with
    | W.Str -> (S.TRegex Pat.all)
    | W.Prim p -> (S.TPrim p)
    | W.Bool -> (S.TUnion (Some "Bool", S.TPrim "True", S.TPrim "False"))
    | W.Union (t1, t2) -> (S.TUnion (None, embed_typ t1, embed_typ t2))
    | W.Inter (t1, t2) -> (S.TInter (None, embed_typ t1, embed_typ t2))
    | W.Arrow (None, args, var, r) -> (S.TArrow ((* None,  *)map embed_typ args, opt_map embed_typ var, embed_typ r))
    | W.Arrow (Some this, args, var, r) -> (S.TArrow ((* None, *) (embed_typ this):: (map embed_typ args), opt_map embed_typ var, embed_typ r))
    | W.This t -> (S.TThis (embed_typ t))
    | W.Object flds -> (object_typ flds)
    | W.With(t, flds) -> (match object_typ flds with
      | S.TObject objflds -> (S.TWith(embed_typ t, objflds))
      | _ -> failwith "absurd")
    | W.Pat pat -> (S.TRegex pat)
    | W.Ref t -> (S.TRef (None, embed_typ t))
    | W.Source t -> (S.TSource (None, embed_typ t))
    | W.Top -> (S.TTop)
    | W.Bot -> (S.TBot)
    | W.Syn x -> (S.TId x)
    | W.TId x -> S.TId x
    | W.App (t1, t2s) -> begin
      let t = typ t1 in
      match JQ.extract_t t with
      | S.TPrim "Constructing"
      | S.TPrim "Mutable"
      | S.TPrim "Immutable" -> begin
        let ss = map sigma t2s in
        let sts = List.filter_map (fun s -> match s with JQ.STyp t -> Some (JQ.extract_t t) | _ -> None) ss in
        if (List.length ss = List.length sts)
        then S.TApp (JQ.extract_t t, sts)
        else JQ.extract_t (JQ.TApp (t, ss))
      end
      (* Hack to make sure special function primitives are multiplicities, not types *)
      | _ -> 
        JQ.extract_t (JQ.TApp(t, map (fun w -> match sigma w with
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "childrenOf"), _)) as a)
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "parentOf"), _)) as a) 
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "prevSibOf"), _)) as a) 
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "nextSibOf"), _)) as a)
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "findOf"), _)) as a)
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "parentsOf"), _)) as a) 
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "prevAllOf"), _)) as a) 
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "nextAllOf"), _)) as a)
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "oneOf"), _)) as a)
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "filterSel"), _)) as a) -> 
          JQ.SMult (JQ.MPlain a)
        | s -> s) t2s))
    end
    | W.Forall (x, s, t) -> 
      let s = sigma s in
      let t = typ t in
      let t' = match s with
        | JQ.STyp _ -> t
        | JQ.SMult _ -> JQ.mult_typ_subst x (JQ.MId x) t in
      JQ.extract_t (JQ.TForall (None, x, s, t'))
    | W.Rec (x, t) -> (S.TRec (None, x, embed_typ t))
    | W.Lambda (args, t) -> 
      let args = map (second2 JQ.embed_k) (map id_kind args) in
      let t = typ t in
      let t' = List.fold_left (fun t (x, k) -> match k with
        | JQ.KMult _ -> JQ.mult_typ_subst x (JQ.MId x) t
        | _ -> t) t args in
      JQ.extract_t (JQ.TLambda (None, args, t'))
    | W.Fix (x, k, t) -> let (x, k) = id_kind (x, k) in (S.TFix (None, x, k, embed_typ t)))
      
  and opt_map f v = match v with None -> None | Some v -> Some (f v)
  and embed_typ t = JQ.extract_t (typ t)

  and id_kind (id, k) = 
    let rec helper k = match k with
      | W.KStar -> S.KStar
      | W.KArrow (args, ret) -> S.KArrow (map helper args, helper ret)
      | W.KMult m -> match helper m with
        | S.KEmbed m -> S.KEmbed (JQ.KMult m)
        | m -> S.KEmbed (JQ.KMult (JQ.KStrobe m))
    in (id, helper k)

  and sigma (writ_sig : W.s) : JQ.sigma = match writ_sig with 
    | W.Mult m -> JQ.SMult (mult m)
    | W.Typ t -> JQ.STyp (typ t)

  and mult (writ_mult : W.m) : JQ.multiplicity =
    match writ_mult with
    | W.Plain t -> JQ.MPlain (typ t)
    | W.MId id -> JQ.MId id
    | W.One m -> JQ.MOne (mult m)
    | W.Zero m -> JQ.MZero (mult m)
    | W.ZeroOne m -> JQ.MZeroOne (mult m)
    | W.OnePlus m -> JQ.MOnePlus (mult m)
    | W.ZeroPlus m -> JQ.MZeroPlus (mult m)
    | W.Sum (m1, m2) -> JQ.MSum(mult m1, mult m2)

  and fld (writ_fld : W.f) : S.field = match writ_fld with
    | W.Present (pat, t) -> (pat, S.Present, embed_typ t)
    | W.Maybe (pat, t) -> (pat, S.Maybe, embed_typ t)
    | W.Inherited (pat, t) -> (pat, S.Inherited, embed_typ t)
    | W.Absent pat -> error "fld applied to Absent"
    | W.Skull _ -> error "fld applied to Skull"
    | W.Star _ -> error "fld applied to Star"

  and object_typ (flds : W.f list) : S.typ =
    let (flds_no_absents, absent_pat) =
      let (absents, others) = List.partition is_absent flds in
      (others,
       Pat.unions (List.map pat_of absents)) in
    let (flds_no_stars, absent_pat) =
      let (stars, others) = List.partition is_star flds_no_absents in
      match stars with
      | [] -> let skulls = List.filter is_skull others in
              begin match skulls with
              | [] -> (others, absent_pat)
              | _ -> error "BAD is nonsensical without *"
              end
      | [W.Star opt_star_typ] ->
        let star_pat =
          Pat.negate (Pat.unions (absent_pat::(map pat_of others))) in
        begin match opt_star_typ with
        | None -> (others, Pat.union star_pat absent_pat)
        | Some t -> ((W.Maybe (star_pat, t)) :: others, absent_pat)
        end
      | _ -> error "multiple stars (*) in an object type" in
    (* TODO(arjun): Why is this overlap check here? Can we do it at the top
       of the function? *)
    List.iter_pairs assert_overlap
      (absent_pat :: (List.map pat_of flds_no_stars));
    let flds_no_skulls_stars =
      List.filter (fun f -> not (is_skull f)) flds_no_stars in
    S.TObject (S.mk_obj_typ (map fld flds_no_skulls_stars) absent_pat)


  let empty_structureEnv = 
    ([],
     {children = IdMap.empty;
      parent = IdMap.empty;
      prev = IdMap.empty;
      next = IdMap.empty})
      

  let desugar_typ (p : Pos.t) (wt : W.t) : JQ.typ =
    try JQ.embed_t (JQ.extract_t (typ wt))
    with Typ_stx_error msg ->
      raise (Typ_stx_error (Pos.toString p ^ msg))


  (* Consumes: 
     dcs (declComp list): list of top-level declComps
     Produces: dcs

     Recursively traverses the local structure defined by dcs, 
     and performs several well-formedness checks. Rejects
     malformed structures by raising Local_structure_error exceptions
     Produces: original dcs, otherwise raises exception
     
     Well-formedness rules: 
     1) Cannot have more than one DeclComp with the same id
     2) DIds can only appear on the same level as a previous sibling
        DNested declComp with the same id
     4) Cannot have two consecutive placeholders  *)
  let well_formed_structure (dcs : W.declComp list) : W.declComp list =

    (* Helper: raises Local_structure_error with 
       "Local structure is not well-formed: msg" *)
    let raise_lse msg = 
      raise (Local_structure_error 
               ("Local structure is not well-formed: " ^ msg)) in
    
    (* Helper: raises exception if id is in defined, otherwise adds *)
    let check_add defined id = 
      if IdSet.mem id defined then
        raise_lse ("id " ^ id ^ " has already been defined")
      else IdSet.add id defined in
        
    (* Consumes :
       defined IdSet.t: presence of id 'x' indicates DeclComp with name 'x'
         has already been found
       dc (W.declComp): the declComp to process
       
       Produces: IdSet: updated set. Raises exception if declComp causes
         well-formedness error *)
    let rec wf_dc (defined : IdSet.t) (dc : W.declComp) : IdSet.t = 

      let (name,_,_,_,content) = dc in

      (* Rule 1 *)
      let new_defined = check_add defined name in

      let wf_dcc dccs = 
        let rec helper acc dccs = 
          let (local_defined, defined) = acc in 
          match dccs with
          | [] -> acc
          | hd::tl -> begin match hd, tl with
            | W.DNested ((cname,_,_,_,_) as child), _ ->
              helper
                ((check_add local_defined cname) (* Rule 1 *),
                 (wf_dc defined child) (* check child declComp*))
                tl
            | W.DId cname, _ ->
              (* Rules 2 and 3 *)
              if IdSet.mem cname local_defined then helper acc tl else
                raise_lse ("DId " ^ cname ^ " does not have a previous sibling declComp with the same name")
            | W.DPlaceholder, (W.DPlaceholder::rest) -> 
              (* Rule 4 *)
              raise_lse "encountered two adjacent placeholders"
            | W.DPlaceholder, _ -> helper acc tl
          end in (* end helper *)
        
        snd (helper (IdSet.empty, new_defined) dccs) in (* end wf_dcc *)
      
      (* Check content and return updated defined *)
      wf_dcc content in (* end wf_dc *)
        
    (* Check for well-formedness *)
    
    (* Do nothing if empty list, otherwise check *)
    (match dcs with | [] -> () | hd::tl ->
      ignore(
        List.fold_left wf_dc
        (* Call wf_dc on first to start fold with a tuple *)
          (wf_dc IdSet.empty hd) tl
      ));

    (* If we've checked everything succesfully, just return original list *)
    dcs

      

  (* Consumes a list of top-levels declComps, and compiles the structure
   they represent into a structureEnv. Also compiles a list of bindings
     to be added to the env. Produces this list of bindings along with
     the compiled structureEnv.
  
     PRECONDITION: dcs must have already passed the well-formed test *)
  let desugar_structure (dcs : W.declComp list) : (typ IdMap.t * structureEnv) =

    (* Consumes: List of top-level declComps.
       Produces: declComp IdMap.t

       Gather all declComps in an IdMap. This could be done on the fly
       for efficiency's sake but it's cleaner just to get it done before
       compilation. *)
    let defined = 
      let rec gdc defined dc = 
        let (name,_,_,_,content) = dc in
        let new_defined = IdMap.add name dc defined in
        (* Traverse over the contents and return *)
        List.fold_left (fun defined dcc -> match dcc with
        | W.DNested dc -> gdc defined dc (* Only gather for DNested *)
        | W.DPlaceholder
        | W.DId _ -> defined) new_defined content in
      (* gather defined maps for  each top-level dc *)
      List.fold_left gdc IdMap.empty dcs in

    
    (** Function : gen_bindings
        ============================================================
        This function takes a list of declComps and generates bindings from ids to 
        TDoms based on information given in the declComp. The TDoms generated
        by this function include required classes, optional classes, and ids.
    **)
    let gen_bindings (dcs : W.declComp list) : typ IdMap.t =
      let generateSels ((classes, optClasses, ids) : W.attribs) (comb : Css.combinator) (sel : Css.t) (node : string) : Css.t =
        let nodesel = node in
        let clsel = if classes = [] then "" else 
            ".!" ^ (String.concat ".!" classes) in
        let optclsel = if optClasses = [] then "" else
            ".?" ^ (String.concat ".?" optClasses) in
        let idsel = if List.length ids = 1 then "#" ^ (List.hd ids) else "" in
        let simple = Css.singleton (nodesel ^ clsel ^ optclsel ^ idsel) in
        match comb with
        (* The Desc combinator should only be used as a dummy value *)
        | Css_syntax.Desc -> simple
        | _ -> Css.concat_selectors sel comb simple in
      let rec compileComp (ids : typ IdMap.t) (dc : W.declComp) (comb : Css.combinator) (prev : Css.t) = 
        let (name,_,nodeType,attribs, content) = dc in
        let sels = generateSels attribs comb prev nodeType in
        let new_ids = 
          IdMap.add 
            name 
            (JQ.TDom (None,name, JQ.TStrobe (S.TId ((String.capitalize nodeType) ^ "Element")), sels))
            ids in
        compileContent new_ids content Css_syntax.Kid sels

      and compileContent (ids : typ IdMap.t) (dccs : W.dcContent list) (comb : Css.combinator) (prev : Css.t)  : typ IdMap.t = match dccs with
        | [] -> ids
        | (W.DId name) :: tail ->
          (* Get decl from defined map *)
          let decl = begin try IdMap.find name defined
            with Not_found -> failwith 
              ("id " ^ name ^ " used before declared in structure declaration." ^
                  " This declaration SHOULD have been rejected in well-formed" ^
                  " testing") end in
          let (_, _, nodeType, attribs, contents) = decl in
          let sels = generateSels attribs comb prev nodeType in
          let tdom = try IdMap.find name ids with Not_found -> 
            failwith "gen_bindings:compile_content: IMPOSSIBLE?: should not encounter a name for which there is no typ in ids"
            (* JQ.TDom (None,  *)
            (*          name *)
            (*          JQ.TStrobe (S.TId ((String.capitalize nodeType) ^ "Element")),  *)
            (*          Css.empty) in begin *) in begin
          match tdom with
          | JQ.TDom (_, _, _, sels2) -> compileContent 
            (IdMap.add name 
               (JQ.TDom (None, 
                         name, 
                         JQ.TStrobe (S.TId ((String.capitalize nodeType) 
                                            ^ "Element")), 
                         Css.union sels sels2)) ids) tail Css_syntax.Adj sels
          | _ -> failwith "impossible"
          end
        | [W.DNested d] ->
          compileComp ids d comb prev

        | (W.DNested ((name, _, nodeType, attribs, content) as d))::W.DPlaceholder::tail -> 
          let sels = generateSels attribs comb prev nodeType in
          let newMap = compileComp ids d comb prev in
          compileContent newMap tail Css_syntax.Sib sels

        | (W.DNested ((name, _, nodeType, attribs, content) as d))::tail ->
          let sels = generateSels attribs comb prev nodeType in
          let newMap = compileComp ids d comb prev in
          compileContent newMap tail Css_syntax.Adj sels

        | _::tail -> compileContent ids tail comb prev in

      (* Fold over all dcs and merge bindings *)
      List.fold_left (fun all_bindings dc ->
        compileComp all_bindings dc Css_syntax.Desc Css.all) 
        IdMap.empty dcs in
        
    (** Function: compile
        ============================================================
        Compile takes a structure environment (the accumulator) and a declaration component, compiles structure information from the declComp and adds it to the existing structureEnv. TODO(liam) Currently it does not touch the backformEnv, 
        suggesting that perhaps it should only deal with the clauseEnv
    **)
    let compile (senv : structureEnv) (dcs : W.declComp list)  : structureEnv = 

      let element = "Element" in
      let any = "Any" in
      let (benv,_) = senv in
      
      (** Function: enforcePresence
          ==================================================
          Takes an id, a preClauseEnv, and looks up each of the preClauseMaps in the preClauseEnv to determine if id is present. If it is present, the preClauseMap is preserved, otherwise the function adds a binding from id to an empty list in the preClauseMap.
      **)
      let enforcePresence (id : id) (pcenv : preClauseEnv) : preClauseEnv =
        let helper (pcm : preClauseMap) =
          if (IdMap.mem id pcm) then pcm else (IdMap.add id [] pcm) in
        {pce_children = (helper pcenv.pce_children);
         pce_parent =  (helper pcenv.pce_parent);
         pce_prev = (helper pcenv.pce_prev);
         pce_next = (helper pcenv.pce_next) } in



      (** Function: compileComp
          ==================================================
          Similar to compile, compileComp takes a preStructureEnv and declComp and adds the structure information in declComp to the preStructureEnv.
      **)
      let rec compileComp (psenv : (preStructureEnv)) (dc : W.declComp)
          : preStructureEnv =

        let (benv, pcenv) = psenv in

        (* parts of dc, which is the 'parent' *)
        let (pname, _, nodeType, (classes, optClasses, ids), pcontents) = dc in

        (*** Helper functions *)
        (** Function: update
            ==================================================
            update takes a source id, a target id option, a preClauseMap and adds the binding from source id to target id option to the preClauseMap. It assumes that the presence of source id is already enforced in the preClauseMap.
        **)
        let update (source : id) (target : id option) (pcm : preClauseMap) 
            : preClauseMap =
          if (IdMap.mem source pcm) then 
            (IdMap.add source (target::(IdMap.find source pcm)) pcm)
          else failwith ("Id: " ^source ^"  not yet in preClauseMap") in

        (** Function: compPreClauses
            ==================================================
            Takes a preClauseEnv, a list of dcContents (the children list of a declComp), compiles the list of dcContents and merges the result into the pcenv. This is the core function for compiling declarations into clause environments.
        **)
        let  compPreClauses (pcenv : preClauseEnv) (dccs : W.dcContent list) : preClauseEnv = 

          let pcenv = match dccs with 
            | [] -> pcenv
            | hd::_ ->  begin match hd with 
              | W.DPlaceholder -> pcenv
              | W.DNested (name,_,_,_,_)
              | W.DId name ->
                { pce_parent = pcenv.pce_parent; 
                  pce_children = pcenv.pce_children; 
                  pce_prev = update name (Some any) pcenv.pce_prev; 
                  pce_next = pcenv.pce_next} 
            end in

          let rec helper pcenv dccs = 

          (* decompose the pcenv into four preClauseMaps *)
            let { pce_parent = parent; pce_children = children; pce_prev = prev; pce_next = next} = pcenv in
          (* While traversing the list of dcContents, we only update the preClauseMaps relevant to the head of the content list in each of the cases. The rest will be dealt with by recursive calls to the tail of the list. *)
            match dccs with
          (* list is empty ==> return the original pcenv *)
            | [] -> pcenv
          (* list consists of a single placeholder ==> add the binding from parentId to None in kidMap *)
            | W.DPlaceholder :: [] -> 
              {pce_children = (update pname None children);
               pce_parent = parent;
               pce_prev = prev; 
               pce_next = next }
          (* list consists of a single declaration (or Did) ==> add the binding from parentId to id in kidMap, and from id to parentId in parentMap. Also
             indicate that next for name has an Any*)
            | W.DNested  (name,_,_,_,_) :: []
            | W.DId name::[] -> 
              {pce_children = (update pname (Some name) children);
               pce_parent = (update name (Some pname) parent);
               pce_prev = prev; 
               pce_next = (update name (Some any) next) }
          (* list contains more than one element ==> match on the first two elements of the list *)
            | c1 :: ((c2 :: rest) as tail) -> (match c1, c2 with
            (* two placeholders ==> recur on tail *)
              | W.DPlaceholder, W.DPlaceholder -> helper pcenv tail
            (* placeholder and nested/id ==> add binding from parentId to None in kidMap, and bindng from id to None in prevSibMap *)
              | W.DPlaceholder, W.DNested (name, _, _, _, _)
              | W.DPlaceholder, W.DId name -> helper 
                {pce_children = (update pname None children);
                 pce_parent = parent;
                 pce_prev = (update name None prev);
                 pce_next = next; } tail
            (* nested/id and placeholder ==> add binding from parentId to id in kidMap, from id to parentId in parentMap, and from id to None in nextSibMap *)
              | W.DNested (name, _, _, _, _), W.DPlaceholder
              | W.DId name, W.DPlaceholder -> 
                begin match rest with
                | []
                | W.DPlaceholder :: _ -> helper 
                  {pce_children = (update pname (Some name) children);
                   pce_parent = (update name (Some pname) parent);
                   pce_prev = prev;
                   pce_next = (update name None next); } tail
                | W.DNested (name2, _, _, _, _)::_
                | W.DId name2 :: _ -> helper
                  {pce_children = (update pname (Some name) children);
                   pce_parent = (update name (Some pname) parent);
                   pce_prev = (update name2 (Some name) prev);
                   pce_next = (update name None (update name (Some name2) next)); } tail
                end
            (* nested/id and nested/id ==> add binding from parentId to id1 and id2 in kidMap, from id1 and id2 to parentId in parentMap, from id1 to id2 in nextSibMap, from id2 to id1 in prevSibMap *)
              | W.DNested (name1, _, _, _, _), W.DNested (name2, _, _, _, _)
              | W.DNested (name1, _, _, _, _), W.DId name2
              | W.DId name1, W.DNested (name2, _, _, _, _)
              | W.DId name1, W.DId name2 -> helper 
                {pce_children = (update pname (Some name1) children);
                 pce_parent = (update name1 (Some pname) parent);
                 pce_prev = (update name2 (Some name1) prev);
                 pce_next = (update name1 (Some name2) next)} tail) in

          helper pcenv dccs in


        (* Enforce all ids that show up (regardless of whether or not it has been declared before) in the W.declComp *)
        let enforcedPreClauseEnv = List.fold_left (fun pcenv dcc -> match dcc with
          | W.DNested (name,_,_,_,_)
          | W.DId name -> enforcePresence name pcenv
          | _ -> pcenv)
          (enforcePresence pname pcenv) pcontents in

        (* For the first contents, if it is a DNested 
           or a DId, add Any to prev *)

        (*  preClauseEnv updated for this W.declComp *)
        let newPreClauseEnv =  compPreClauses enforcedPreClauseEnv pcontents in

        (* Now compile the contents  *)
        List.fold_left (fun psenv dcc -> 
          match dcc with
          | W.DNested dc -> compileComp psenv dc
          | _ -> psenv)
          (benv, newPreClauseEnv)
          pcontents in

      (* Body of compile *)

      (* start with empty preStructureEnv *)
      let empty_psenv =
        ([],
         {pce_children = IdMap.empty;
          pce_parent = IdMap.empty;
          pce_prev = IdMap.empty;
          pce_next = IdMap.empty}) in


      (* Compile each top-level declComp *)
      let (_, pcenv) = List.fold_left 
        compileComp
        empty_psenv dcs in

      (** Function: transformPCM
          ==================================================
          transformPCM takes a preClauseMap, and a function that takes an id option list (the values in preClauseMaps) and turns the list into a multiplicity. It returns the clauseMap transformed from the preClauseMap. The function argument is used for computing multiplicities from id option lists based on different rules for the different clauseMaps. See transform_children, transform_sibs, transform_parent for more detail.
      **)
      let transformPCM (pcm : preClauseMap) (f : id option list -> multiplicity) = 
        IdMap.fold (fun id ids cm -> 
          IdMap.add id (f ids) cm)
          pcm IdMap.empty in
      
      (* Functions for transforming lists of tids into multiplicities *)
      
      (* Helper function: transform id into MPlain *)
      let wrap_id id = (JQ.MPlain (JQ.TStrobe (S.TId id))) in

      (* Helper: takes an id option and produces a typ. Also
         handles "Any" -> TTop transformation *)
      let extract_id (ido : id option) : S.typ  = match ido with 
        | Some "Any" -> S.TTop
        | Some id -> S.TId id
        | None -> S.TId element in

      (** Function: transform_children
          ==================================================
          Transform function for kidMap that takes an id option list and turns it into a multiplicity.
          Match cases:
          empty list ==> 0<TTop>
          list with a single id ==> 1<id>
          list with a single None ==> 0+<Element>
          list with more than one entries ==> 
             1+<union of remove_dups of all entries in the list>
      **)
      let transform_children idos = let open JQ in match idos with 
        | [] -> MZero (MPlain (TStrobe (S.TTop)))
        | [Some id] -> MOne (wrap_id id)
        | [None] -> MZeroPlus (wrap_id element)
        | _ -> match ListExt.remove_dups idos with
          | [] -> failwith 
            "Desugar:desugar_structure:transform_children: IMPOSSIBLE:";
          | [ido] -> MOnePlus (MPlain (TStrobe (extract_id ido)))
          | hd::tail -> 
            MOnePlus (MPlain (TStrobe (List.fold_left (fun acc ido ->
              S.TUnion (None,acc, (extract_id ido))) 
                                         (extract_id hd) tail))) in
      (** Function: transform_sibs
          ==================================================
          Transform function for prevSibMap and nextSibMap that takes an id option list and turns it into a multiplicity.
          Match cases:
          empty list ==> fail - should not encounter this case
          [Some "Any"] -> 0<TTop>
          list with a single id ==> 1<id>
          list with a single None ==> 01<Element>
          list with more than one entries ==> 
          1<union of all remove_dups entries in the list> OR
          01<union of remove_dups of all entries in the list> if list contains
          an "Any"
      **)
      let transform_sibs idos = let open JQ in match idos with
        | [] -> failwith "Desugar:desugar_structure:transform_sibs: IMPOSSIBLE: should not encounter an empty list of ids."
        | [Some "Any"] -> MZero (MPlain (TStrobe (S.TTop)))
        | [Some id] -> MOne (wrap_id id)
        | [None] -> MZeroOne (wrap_id element)
        (* Any other list with length > 1 *)
        | _ -> begin 
          let rd_idos = ListExt.remove_dups idos in
          let any_present = (List.exists (fun ido -> 
            ido = (Some "Any")) rd_idos) in
          match  (if any_present then (List.filter (fun ido -> 
            (not (ido = (Some "Any")))) rd_idos) 
            else rd_idos) with 
          | [] -> failwith "Desugar:desugar_structure:transform_sibs: IMPOSSIBLE: 
will always have list with length >= 1"
          | hd::tail -> 
            let mplain = 
              MPlain (TStrobe (List.fold_left (fun acc ido -> 
                S.TUnion (None,acc, (extract_id ido))) 
                                 (extract_id hd) tail)) in
            if any_present then MZeroOne mplain else MOne mplain
        end in


      (** Function: transform_parent
          ==================================================
          Transform function for parentMap that takes an id option list and turns it into a multiplicity.
          Match cases:
          empty list ==> 01<Element>
          list with a single id ==> 1<id>
          list with a single None ==> error : parentMap shouldn't have a binding that maps to a placeholder
          list with more than one entries ==> error
      **)
      let transform_parent idos = 
        let open JQ in 
        (* Remove dups first - we have have come across multiple children with
           same name *)
        match (List.remove_dups idos) with
        | [] -> MZeroOne (wrap_id element)
        | [Some id] -> MOne (wrap_id id)
        | [None] -> failwith "parent cannot be a placeholder"
        | hd:: tail -> failwith "cannot have more than one parent" in

      (* Make sure that each  toplevel declComp has nextsib and prevsib
         of 01<Element> *)
      let pcenv = List.fold_left (fun pcenv dc ->
        let (name, _,_,_,_) = dc in
        {pce_children = pcenv.pce_children;
         pce_parent = pcenv.pce_parent;
         pce_prev = IdMap.add name [None] pcenv.pce_prev;
         pce_next = IdMap.add name [None] pcenv.pce_next;})
        pcenv dcs in


      (* Transform clauseEnv, and add Element clauses *)

      let cenv = 
        {children = 
            IdMap.add element (JQ.MZeroPlus (wrap_id element)) 
              (transformPCM pcenv.pce_children transform_children);
         parent = IdMap.add element (JQ.MZeroOne (wrap_id element)) 
            (transformPCM pcenv.pce_parent transform_parent);
         prev = IdMap.add element (JQ.MZeroOne (wrap_id element)) 
            (transformPCM pcenv.pce_prev transform_sibs);
         next = IdMap.add element (JQ.MZeroOne (wrap_id element)) 
            (transformPCM pcenv.pce_next transform_sibs)} in

      
      (* return final structureEnv *)
      (benv, cenv) in

    (* body of desugar_structure *)

    (* generate bindings to add to environment *)
    let bindings = gen_bindings dcs in
    
    (* compile structure into senv. *)

    let (_, cenv) = compile empty_structureEnv dcs in
    
    (* use bindings to create benv *)
    let benv = IdMap.bindings
      (IdMap.map (fun t -> match t with
      | JQ.TDom (_, _,  _, sel) -> sel
      | _ -> failwith "impossible: gen_bindings should only produce bindings from ids to TDoms") bindings) in
    
    (* return list if bindings to add to the environment, and the compiled
       structureEnv *)
    (bindings, (benv, cenv))
      
end 
