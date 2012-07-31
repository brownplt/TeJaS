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
  type clauseMap = multiplicity IdMap.t
  type backformMap = id list StringMap.t
  type backformEnv = { classes : backformMap;
                       optClasses : backformMap;
                       ids :  backformMap }

  type clauseEnv = { children : clauseMap; 
                     parent : clauseMap; 
                     prev : clauseMap;
                     next : clauseMap }
  type structureEnv = (backformEnv * clauseEnv)
  exception Typ_stx_error of string
  val desugar_typ : Pos.t -> W.t -> typ
  val desugar_structure : Pos.t -> structureEnv ->  W.declComp -> (typ IdMap.t * structureEnv) 
  val empty_structureEnv : structureEnv
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
  with type multiplicity = JQ.multiplicity) =
struct
  type typ = JQ.typ
  type kind = JQ.kind
  type multiplicity = JQ.multiplicity
  module Css = JQ.Css

  exception Typ_stx_error of string

  (* Local Structure types *)
  type preClauseMap = id option list IdMap.t
  type clauseMap = multiplicity IdMap.t
  type backformMap = id list StringMap.t

  type backformEnv = { classes : backformMap;
                       optClasses : backformMap;
                       ids :  backformMap }

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

  (* END Local Structure types *)

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
        | JQ.STyp ((JQ.TApp (JQ.TStrobe (S.TPrim "nextAllOf"), _)) as a) -> 
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
    ({classes = StringMap.empty;
      optClasses = StringMap.empty;
      ids = StringMap.empty;},
     {children = IdMap.empty;
      parent = IdMap.empty;
      prev = IdMap.empty;
      next = IdMap.empty})
      

  let desugar_typ (p : Pos.t) (wt : W.t) : JQ.typ =
    try JQ.embed_t (JQ.extract_t (typ wt))
    with Typ_stx_error msg ->
      raise (Typ_stx_error (Pos.toString p ^ msg))

  
  let desugar_structure (p : Pos.t) (senv : structureEnv) (dc : W.declComp) : 
      (typ IdMap.t * structureEnv) = 
    
    (** Function : gen_bindings
        ============================================================
        This function takes a declComp and generates bindings from ids to TDoms based on information given in the declComp. As of now the TDoms generated by this function only contain the required classes selector.
    **)
    let gen_bindings (dc : W.declComp) : typ IdMap.t =
      let generateSels ((classes, optClasses, ids) : W.attribs) : Css.t =
        let clsel = "." ^ (String.concat "." classes) in
        (* TODO: Account for ids and optional classes
           let optclsels = clsel :: (List.map ((^) (clsel ^ ".")) optClasses) in
           let idsels = List.flatten 
           (List.map (fun id -> List.map ((^) ("#" ^ id)) optclsels) ids) in *)
        Css.singleton clsel in
      let rec compileComp (ids : typ IdMap.t) (dc : W.declComp) = 
        let (name,_,nodeType,attribs, content) = dc in
        let new_ids = 
          IdMap.add 
            name 
            (JQ.TDom (None,JQ.TStrobe (S.TId nodeType), generateSels attribs)) 
            ids in
        
        List.fold_left (fun ids dcc -> 
          match dcc with
          | W.DNested dc -> compileComp ids dc
          | _ -> ids ) new_ids content in
      compileComp IdMap.empty dc in

    (** Function: compile
        ============================================================
        Compile takes a structure environment (the accumulator) and a declaration component, compiles structure information from the declComp and adds it to the existing structureEnv.
    **)
    let compile (senv : structureEnv) (dc : W.declComp)  : structureEnv = 
      
      let element = "Element" in
      
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
        (** Function: add2backfromMap
            ==================================================
            add2backfromMap takes an id, a list of strings (required classes, ids, optional classes), a backformMap, and adds the bindings from each of the strings to the id into backformMap.
        **)
        let add2backformMap (id : id) (strs : string list) (bm : backformMap) 
            : backformMap =
          List.fold_left (fun bm s ->
            let toAdd = 
              if StringMap.mem s bm then (id::(StringMap.find s bm)) else [id] in
            StringMap.add s toAdd bm) bm strs in


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
        let rec compPreClauses (pcenv : preClauseEnv) (dccs : W.dcContent list) : preClauseEnv = 
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
          (* list consists of a single declaration (or Did) ==> add the binding from parentId to id in kidMap, and from id to parentId in parentMap *)
          | W.DNested  (name,_,_,_,_) :: []
          | W.DId name::[] -> 
            {pce_children = (update pname (Some name) children);
             pce_parent = (update name (Some pname) parent);
             pce_prev = prev; 
             pce_next = next }
          (* list contains more than one element ==> match on the first two elements of the list *)
          | c1 :: ((c2 :: rest) as tail) -> (match c1, c2 with
            (* two placeholders ==> recur on tail *)
            | W.DPlaceholder, W.DPlaceholder -> compPreClauses pcenv tail
            (* placeholder and nested/id ==> add binding from parentId to None in kidMap, and bindng from id to None in prevSibMap *)
            | W.DPlaceholder, W.DNested (name, _, _, _, _)
            | W.DPlaceholder, W.DId name -> compPreClauses 
              {pce_children = (update pname None children);
               pce_parent = parent;
               pce_prev = (update name None prev);
               pce_next = next; } tail
            (* nested/id and placeholder ==> add binding from parentId to id in kidMap, from id to parentId in parentMap, and from id to None in nextSibMap *)
            | W.DNested (name, _, _, _, _), W.DPlaceholder
            | W.DId name, W.DPlaceholder -> 
              begin match rest with
              | []
              | W.DPlaceholder :: _ -> compPreClauses 
                {pce_children = (update pname (Some name) children);
                 pce_parent = (update name (Some pname) parent);
                 pce_prev = prev;
                 pce_next = (update name None next); } tail
              | W.DNested (name2, _, _, _, _)::_
              | W.DId name2 :: _ -> compPreClauses
                {pce_children = (update pname (Some name) children);
                 pce_parent = (update name (Some pname) parent);
                 pce_prev = (update name2 (Some name) prev);
                 pce_next = (update name None (update name (Some name2) next)); } tail
              end
            (* nested/id and nested/id ==> add binding from parentId to id1 and id2 in kidMap, from id1 and id2 to parentId in parentMap, from id1 to id2 in nextSibMap, from id2 to id1 in prevSibMap *)
            | W.DNested (name1, _, _, _, _), W.DNested (name2, _, _, _, _)
            | W.DNested (name1, _, _, _, _), W.DId name2
            | W.DId name1, W.DNested (name2, _, _, _, _)
            | W.DId name1, W.DId name2 -> compPreClauses 
              {pce_children = (update pname (Some name1) children);
               pce_parent = (update name1 (Some pname) parent);
               pce_prev = (update name2 (Some name1) prev);
               pce_next = (update name1 (Some name2) next)} tail) in

        
        (* backformEnv updated for this W.declComp *)
        let newBackformEnv = 
          {classes = (add2backformMap pname classes benv.classes);
           optClasses = (add2backformMap pname optClasses benv.optClasses);
           ids = (add2backformMap pname ids benv.ids) } in

        (* Enforce all ids that show up (regardless of whether or not it has been declared before) in the W.declComp *)
        let enforcedPreClauseEnv = List.fold_left (fun pcenv dcc -> match dcc with
          | W.DNested (name,_,_,_,_)
          | W.DId name -> enforcePresence name pcenv
          | _ -> pcenv)
          (enforcePresence pname pcenv) pcontents in

        (*  preClauseEnv updated for this W.declComp *)
        let newPreClauseEnv =  compPreClauses enforcedPreClauseEnv pcontents in

        (* Now compile the contents  *)
        List.fold_left (fun psenv dcc -> 
          match dcc with
          | W.DNested dc -> compileComp psenv dc
          | _ -> psenv)
          (newBackformEnv, newPreClauseEnv)
          pcontents in

      (*** Body of compile ***)

      (* start with empty preStructureEnv *)
      let empty_psenv =
        ({classes = StringMap.empty;
          optClasses = StringMap.empty;
          ids = StringMap.empty;},
         {pce_children = IdMap.empty;
          pce_parent = IdMap.empty;
          pce_prev = IdMap.empty;
          pce_next = IdMap.empty}) in

      let (benv_complete, pcenv) = compileComp empty_psenv dc in

      (** Function: transformPCM
          ==================================================
          transformPCM takes a preClauseMap, and a function that takes an id option list (the values in preClauseMaps) and turns the list into a multiplicity. It returns the clauseMap transformed from the preClauseMap. The function argument is used for computing multiplicities from id option lists based on different rules for the different clauseMaps. See transform_children, transform_sibs, transform_parent for more detail.
      **)
      let transformPCM (pcm : preClauseMap) (f : id option list -> multiplicity) = 
        IdMap.fold (fun id ids cm -> 
          IdMap.add id (f (ListExt.remove_dups ids)) cm)
          pcm IdMap.empty in
      
      (* Functions for transforming lists of tids into multiplicities *)

      let wrap_id id = (JQ.MPlain (JQ.TStrobe (S.TId id))) in

      let extract_id (ido : id option) : id  = match ido with 
        | Some id -> id
        | None -> element in

      (** Function: transform_children
          ==================================================
          Transform function for kidMap that takes an id option list and turns it into a multiplicity.
          Match cases:
          empty list ==> 0<Element>
          list with a single id ==> 1<id>
          list with a single None ==> 0+<Element>
          list with more than one entries ==> 1+<union of all entries in the list>
      **)
      let transform_children idos = let open JQ in match idos with 
        | [] -> MZero (MPlain (TStrobe (S.TTop)))
        | [Some id] -> MOne (wrap_id id)
        | [None] -> MZeroPlus (wrap_id element)
        | hd::tail -> 
          MOnePlus (MPlain (TStrobe (List.fold_left (fun acc ido ->
            S.TUnion (None,acc, (S.TId (extract_id ido)))) 
                                       (S.TId (extract_id hd)) tail))) in
      (** Function: transform_sibs
          ==================================================
          Transform function for prevSibMap and nextSibMap that takes an id option list and turns it into a multiplicity.
          Match cases:
          empty list ==> 0<Element>
          list with a single id ==> 1<id>
          list with a single None ==> 01<Element>
          list with more than one entries ==> 1<union of all entries in the list>
      **)
      let transform_sibs idos = let open JQ in match idos with
        (* what should this be? TTop or Element? *)
        (* Question: Should MZero be a unit constructor? *)
        | [] -> MZero (MPlain (TStrobe (S.TTop)))
        | [Some id] -> MOne (wrap_id id)
        | [None] -> MZeroOne (wrap_id element)
        | hd::tail -> MOne (MPlain (TStrobe (List.fold_left (fun acc ido ->
          S.TUnion (None,acc, (S.TId (extract_id ido)))) 
                                                (S.TId (extract_id hd)) tail))) in

      (** Function: transform_parent
          ==================================================
          Transform function for parentMap that takes an id option list and turns it into a multiplicity.
          Match cases:
          empty list ==> 01<Element>
          list with a single id ==> 1<id>
          list with a single None ==> error : parentMap shouldn't have a binding that maps to a placeholder
          list with more than one entries ==> 1<union of all entries in the list>
      **)
      let transform_parent idos = let open JQ in match idos with
        | [] -> MZeroOne (wrap_id element)
        | [Some id] -> MOne (wrap_id id)
        | [None] -> failwith "parent cannot be a placeholder"
        | hd:: tail -> MOne (MPlain (TStrobe (List.fold_left (fun acc ido ->
          S.TUnion (None,acc, (S.TId (extract_id ido)))) 
                                                (S.TId (extract_id hd)) tail))) in


      (* Make sure that the toplevel declComp has nextsib and prevsib
         of 01<Element>
         Note: this is moderately hackish and disgusting. 
         TODO-liam: make this cleaner later on? *)
      
      let (name, _,_,_,_) = dc in

      let pcenv = {pce_children = pcenv.pce_children;
                   pce_parent = pcenv.pce_parent;
                   pce_prev = IdMap.add name [None] pcenv.pce_prev;
                   pce_next = IdMap.add name [None] pcenv.pce_next;} in
      
      
      (* return final structureEnv, adding bindings for element in each of the maps *)
      let new_benv = benv_complete in
      let new_cenv = {children = IdMap.add element (JQ.MZeroPlus (wrap_id element)) (transformPCM pcenv.pce_children transform_children);
                      parent = IdMap.add element (JQ.MZeroOne (wrap_id element)) (transformPCM pcenv.pce_parent transform_parent);
                      prev = IdMap.add element (JQ.MZeroOne (wrap_id element)) (transformPCM pcenv.pce_prev transform_sibs);
                      next = IdMap.add element (JQ.MZeroOne (wrap_id element)) (transformPCM pcenv.pce_next transform_sibs)} in

      let (old_benv, old_cenv) = senv in
      let bMap_merge (map1 : backformMap) (map2 : backformMap) : backformMap =
        StringMap.merge (fun (k : string) (v1 : id list option) (v2 : id list option) -> 
          match v1,v2 with
          | Some ids1, Some ids2 -> Some (ids1 @ ids2)
          | _, None -> v1
          | None, _ -> v2) map1 map2 in
      let cMap_merge (map1 : clauseMap) (map2 : clauseMap) : clauseMap =
        IdMap.merge (fun (key : id) (v1 : multiplicity option) (v2 : multiplicity option) ->
          match v1, v2 with
          | Some m1, Some m2 -> Some (JQ.MSum (m1, m2))
          | _, None -> v1
          | None, _ -> v2) map1 map2 in
      ({classes = bMap_merge old_benv.classes new_benv.classes;
        optClasses = bMap_merge old_benv.optClasses new_benv.optClasses;
        ids = bMap_merge old_benv.ids new_benv.ids;},
       {children = cMap_merge old_cenv.children new_cenv.children;
        parent = cMap_merge old_cenv.parent new_cenv.parent;
        prev = cMap_merge old_cenv.prev new_cenv.prev;
        next = cMap_merge old_cenv.next new_cenv.next}) in
    
    (* Body of desugar_structure *)
    (gen_bindings dc, compile senv dc)
      

end
