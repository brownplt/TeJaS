open Prelude
open Format
open FormatExt
open LocalStructure_syntax
open JQuery_types
open JQuery_syntax
open TypImpl
open Sig
 
let popEnvWithTDoms (ds : declSyntax) : env =
  let generateSels ((classes, optClasses, ids) : attribs) : Css.t =
    let clsel = "." ^ (String.concat "." classes) in
    (* TODO: Account for ids and optional classes
       let optclsels = clsel :: (List.map ((^) (clsel ^ ".")) optClasses) in
       let idsels = List.flatten 
       (List.map (fun id -> List.map ((^) ("#" ^ id)) optclsels) ids) in *)
    Css.singleton clsel in
  let rec compileComp (env : env) (dc : declComp) = 
    let (Decl (name,_,nodeType,attribs, content)) = dc in
    let tb = (BTypBound
                ((TDom (None,TId nodeType, generateSels attribs)),
                 KStar)) in
    compileContents (IdMap.add name tb env) content 
  and compileContents (env : env) (dccs : dcContent list) =
    List.fold_left (fun env dcc -> 
      match dcc with
      | DNested dc -> compileComp env dc
      | _ -> env)
      env dccs in
  (* Add 'any element' tid *)
  let envWithEmpty = IdMap.add "ElementAny" 
    (* TODO: Css.singleton "*" creates a lexer error *)
    (BTypBound ((TDom (None, TId "Element", Css.singleton "ANY")), KStar)) 
    IdMap.empty in
  List.fold_left compileComp envWithEmpty ds

    

    
let compileStructure (ds : declSyntax) : structureEnv = 

  let enforcePresence (name : string) (pcenv : preClauseEnv) : preClauseEnv =
    let (PreClauseEnv (child,par,prev,next)) = pcenv in
    let helper (pcm : preClauseMap) =
      let id = LSId name in
      if (LSIdMap.mem id pcm) then pcm else (LSIdMap.add id [] pcm) in
    (PreClauseEnv ((helper child), (helper par), (helper prev), (helper next))) in

  (* compileComp *)
  let rec compileComp (psenv : (preStructureEnv)) (dc : declComp) : preStructureEnv =

    (* parts of dc, which is the 'parent' *)
    let (Decl (pname, _, nodeType, (classes, optClasses, ids), pcontents)) = dc in
   
    (*** Helper functions *)
    let add2backformMap (name : string) (strs : string list) 
        (bm : backformMap) : backformMap =
      List.fold_left (fun bm s ->
        let id = (LSId name) in 
        let toAdd = 
          if StringMap.mem s bm then (id::(StringMap.find s bm)) else [id] in
        StringMap.add s toAdd bm) bm strs in
    let update (name : string) (tname : string) (pcm : preClauseMap) : preClauseMap =
      let id = LSId name in
      if (LSIdMap.mem id pcm) then (LSIdMap.add id ((TId tname)::(LSIdMap.find id pcm)) pcm)
      else failwith ("Id: " ^name ^"  not yet in preClauseMap") in

    let rec compPreClauses (pcenv : preClauseEnv) (dccs : dcContent list) : preClauseEnv = 
      let (PreClauseEnv (child,par,prev,next)) = pcenv in
      match dccs with
      | []
      | DPlaceholder :: [] -> pcenv
      | DNested (Decl (name,_,_,_,_)) :: []
      | DId name::[] -> 
        (PreClauseEnv ((update pname name child), 
                       (update name pname par), prev, next))
      | c1 :: ((c2 :: rest) as tail) -> (match c1, c2 with
          (* We only update the head of the list, so that we don't update the same
             name more than once *)
        | DPlaceholder, DPlaceholder -> compPreClauses pcenv tail
        | DPlaceholder, DNested (Decl (name, _, _, _, _))
        | DPlaceholder, DId name -> compPreClauses 
          (PreClauseEnv ((update pname "ElementAny" child), par,
                        (update name "ElementAny" prev), next)) tail
        | DNested (Decl (name, _, _, _, _)), DPlaceholder
        | DId name, DPlaceholder ->
          compPreClauses (PreClauseEnv ((update pname "ElementAny" 
                                           (update pname name child)), 
                                        (update name pname par), prev,
                                        (update name "ElementAny" next))) tail
        | DNested (Decl (name1, _, _, _, _)), DNested (Decl (name2, _, _, _, _))
        | DNested (Decl (name1, _, _, _, _)), DId name2
        | DId name1, DNested (Decl (name2, _, _, _, _))
        | DId name1, DId name2 -> 
          compPreClauses 
            (PreClauseEnv ((update pname name1 child),
                           (update name1 pname par),
                           (update name2 name1 prev),
                           (update name1 name2 next)))
            tail) in

    let (BackformEnv (cBenv, ocBenv, idBenv), pcenv) = psenv in 
    let newBackformEnv = (BackformEnv 
                            ((add2backformMap pname classes cBenv),
                             (add2backformMap pname optClasses ocBenv),
                             (add2backformMap pname ids idBenv))) in

    (* this only enforces the children - the parent declComp is handled separately *)
    let enforcedPreClauseEnv = List.fold_left (fun pcenv dcc -> match dcc with
      | DNested (Decl (name,_,_,_,_))
      | DId name -> enforcePresence name pcenv
      | _ -> pcenv)
      pcenv pcontents in
    let newPreClauseEnv =  compPreClauses enforcedPreClauseEnv pcontents in
    List.fold_left (fun psenv dcc -> 
      match dcc with
      | DNested dc -> compileComp psenv dc
      | _ -> psenv)
      (newBackformEnv, newPreClauseEnv)
      pcontents in

  (**** compile body *)

  (* start with empty preStructureEnv *)
  let (benv, pcenv) =
    ((BackformEnv (StringMap.empty, StringMap.empty, StringMap.empty)),
    (PreClauseEnv (LSIdMap.empty, LSIdMap.empty, LSIdMap.empty, LSIdMap.empty))) in
  
  (* enforce all top-level declComps *)
  let enforcedPcenv = List.fold_left (fun pcenv (Decl (name,_,_,_,_)) ->
    enforcePresence name pcenv)
    pcenv
    ds in

  (* build backformEnv and preClauseEnv *)
  let (benv_complete, (PreClauseEnv (childPCM, parPCM, prevPCM, nextPCM))) = 
    List.fold_left compileComp (benv, enforcedPcenv) ds in

  (* transform preClauseMap -> clauseMap *)
  let transformPCM (pcm : preClauseMap) (f : int -> typ -> multiplicity) = LSIdMap.fold 
    (fun id typs (cm : clauseMap) -> match ListExt.remove_dups typs with
    | [] -> LSIdMap.add id (f 0 TTop) cm
    | hd::tl ->
      let size = List.length tl + 1 in
      let typ = List.fold_left (fun tu t -> TUnion (None,tu, t)) hd tl in
      LSIdMap.add id (f size typ) cm)
    pcm LSIdMap.empty in
  
  let childFun s t = match s with
    | 0 -> MZeroPlus (MPlain (TId "ElementAny"))
    | 1 -> MOne (MPlain t)
    | _ -> MOnePlus (MPlain t) in

  let parFun s t = match s with 
    | 0 -> MZeroOne (MPlain (TId "ElementAny"))
    | 1 -> MOne (MPlain t)
    | _ -> MOne (MPlain t) in
  
  let prevNextFun s t = match s with 
    | 0 -> MZero (MPlain t)
    | 1 -> MOne (MPlain t) 
    | _ -> MOne (MPlain t) in

  (* (transformPreClauseEnv pcenv_complete) *)
  (benv_complete, (ClauseEnv ((transformPCM childPCM childFun),
                              (transformPCM parPCM parFun),
                              (transformPCM prevPCM prevNextFun),
                              (transformPCM nextPCM prevNextFun))))

let print_structureEnv senv = 
  let (BackformEnv (classes, optClasses, ids), 
       ClauseEnv (childMap,parMap,prevMap,nextMap)) = senv in
  let print_lsid (LSId id) = text id in
  let print_benv_key = text in
  let print_benv_val ids = 
    horzOrVert (List.fold_left (fun a id -> (print_lsid id)::a) [] ids) in
  let print_cenv_key = print_lsid in
  let print_cenv_val = TypImpl.Pretty.multiplicity in
  vert [text "Backform Environment";
        (StringMapExt.p_map "Classes" empty print_benv_key print_benv_val classes);
        (StringMapExt.p_map "Optional Classes" empty print_benv_key print_benv_val optClasses);
        (StringMapExt.p_map "Ids" empty print_benv_key print_benv_val ids);
        text "Clause Environment";
        (LSIdMapExt.p_map "Children Clause" empty print_cenv_key print_cenv_val childMap);
        (LSIdMapExt.p_map "Parent Clause" empty print_cenv_key print_cenv_val parMap);
        (LSIdMapExt.p_map "Prev Sib Clause" empty print_cenv_key print_cenv_val prevMap);
        (LSIdMapExt.p_map "Next Sib Clause" empty print_cenv_key print_cenv_val nextMap);];






