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
      | _ -> JQ.extract_t (JQ.TApp (t, map sigma t2s))
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
    
    (* Generate TDom bindings *)
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


    (*     compileContents new_ids content *)
    (*   and compileContents ids dcc = List.fold_left (fun ids dcc ->  *)
    (*     match dcc with *)
    (*     | W.DNested dc -> compileComp ids dc *)
    (*     | _ -> ids ) ids dccs  in *)
    (*   compileComp IdMap.empty dc                                                     *)
        
    (* in  *)

    (* Compile structure *)
    let compile (senv : structureEnv) (dc : W.declComp)  : structureEnv = 
      
      let element = "Element" in
      
      let enforcePresence (id : id) (pcenv : preClauseEnv) : preClauseEnv =
        let helper (pcm : preClauseMap) =
          if (IdMap.mem id pcm) then pcm else (IdMap.add id [] pcm) in
        {pce_children = (helper pcenv.pce_children);
         pce_parent =  (helper pcenv.pce_parent);
         pce_prev = (helper pcenv.pce_prev);
         pce_next = (helper pcenv.pce_next) } in

      (* compileComp *)
      let rec compileComp (psenv : (preStructureEnv)) (dc : W.declComp)
          : preStructureEnv =

        let (benv, pcenv) = psenv in

        (* parts of dc, which is the 'parent' *)
        let (pname, _, nodeType, (classes, optClasses, ids), pcontents) = dc in
        (*** Helper functions *)
        let add2backformMap (id : id) (strs : string list) (bm : backformMap) 
            : backformMap =
          List.fold_left (fun bm s ->
            let toAdd = 
              if StringMap.mem s bm then (id::(StringMap.find s bm)) else [id] in
            StringMap.add s toAdd bm) bm strs in

        let update (source : id) (target : id option) (pcm : preClauseMap) 
            : preClauseMap =
          if (IdMap.mem source pcm) then 
            (IdMap.add source (target::(IdMap.find source pcm)) pcm)
          else failwith ("Id: " ^source ^"  not yet in preClauseMap") in

        let rec compPreClauses (pcenv : preClauseEnv) (dccs : W.dcContent list) : preClauseEnv = 
          let { pce_parent = parent; pce_children = children; pce_prev = prev; pce_next = next} = pcenv in
          match dccs with
          | [] -> pcenv
          | W.DPlaceholder :: [] -> 
            {pce_children = (update pname None children);
             pce_parent = parent;
             pce_prev = prev; 
             pce_next = next }
          | W.DNested  (name,_,_,_,_) :: []
          | W.DId name::[] -> 
            {pce_children = (update pname (Some name) children);
             pce_parent = (update name (Some pname) parent);
             pce_prev = prev; 
             pce_next = next }
          | c1 :: ((c2 :: rest) as tail) -> (match c1, c2 with
            | W.DPlaceholder, W.DPlaceholder -> compPreClauses pcenv tail
            | W.DPlaceholder, W.DNested (name, _, _, _, _)
            | W.DPlaceholder, W.DId name -> compPreClauses 
              {pce_children = (update pname None children);
               pce_parent = parent;
               pce_prev = (update name None prev);
               pce_next = next; } tail
            | W.DNested (name, _, _, _, _), W.DPlaceholder
            | W.DId name, W.DPlaceholder -> compPreClauses 
              {pce_children = (update pname (Some name) children);
               pce_parent = (update name (Some pname) parent);
               pce_prev = prev;
               pce_next = (update name None next); } tail
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

        (* Enforce everything in the W.declComp *)
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

      (** Body of compile **)

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

      (* transform preClauseMap -> clauseMap *)
      let transformPCM (pcm : preClauseMap) (f : id option list -> multiplicity) = 
        IdMap.fold (fun id ids cm -> IdMap.add id (f (ListExt.remove_dups ids)) cm)
           pcm IdMap.empty in

      (* Functions for transforming lists of tids into multiplicities *)

      let wrap_id id = (JQ.MPlain (JQ.TStrobe (S.TId id))) in

      let extract_id (ido : id option) : id  = match ido with 
        | Some id -> id
        | None -> element in

      let transform_children idos = let open JQ in match idos with 
        | [] -> MZero (wrap_id element)
        | [Some id] -> MOne (wrap_id id) 
        | [None] -> MZeroPlus (wrap_id element)
        | hd::tail -> 
          MOnePlus (MPlain (TStrobe (List.fold_left (fun acc ido ->
            S.TUnion (None,acc, (S.TId (extract_id ido)))) 
                                       (S.TId (extract_id hd)) tail))) in

      let transform_sibs idos = let open JQ in match idos with
        | [] -> MZero (wrap_id element)
        | [Some id] -> MOne (wrap_id id)
        | [None] -> MZeroOne (wrap_id element)
        | _ -> failwith "transform_sibs needs a list of length 1" in

      let transform_parent idos = let open JQ in match idos with
        | [] -> MZeroOne (wrap_id element)
        | [Some id] -> MOne (wrap_id id)
        | [None] -> failwith "parent cannot be a placeholder"
        | _ -> failwith "transform_parent needs a list of length 1" in

      (* Make sure that the toplevel declComp has nextsib and prevsib
         of 01<Element>
         Note: this is moderately hackish and disgusting. 
         TODO-liam: make this cleaner later on? *)
      
      let (name, _,_,_,_) = dc in

      let pcenv = {pce_children = pcenv.pce_children;
                   pce_parent = pcenv.pce_parent;
                   pce_prev = IdMap.add name [None] pcenv.pce_prev;
                   pce_next = IdMap.add name [None] pcenv.pce_next;} in
      
      
      (* return final structureEnv *)
      (benv_complete, 
       {children = IdMap.add element (JQ.MZeroPlus (wrap_id element)) (transformPCM pcenv.pce_children transform_children);
        parent = IdMap.add element (JQ.MZeroOne (wrap_id element)) (transformPCM pcenv.pce_parent transform_parent);
        prev = IdMap.add element (JQ.MZeroOne (wrap_id element)) (transformPCM pcenv.pce_prev transform_sibs);
        next = IdMap.add element (JQ.MZeroOne (wrap_id element)) (transformPCM pcenv.pce_next transform_sibs)}) in

    (* Body of desugar_structure *)
    (gen_bindings dc, compile senv dc)


end
