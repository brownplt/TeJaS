open Prelude
open Sig
open Strobe_sigs
open TypeScript_sigs


module MakeActions
  (StrobeSub : STROBE_SUBTYPING)
  (TypeScript : TYPESCRIPT_MODULE
   with type baseTyp = StrobeSub.typ
  with type baseKind = StrobeSub.kind
  with type baseBinding = StrobeSub.binding
  with type typ = StrobeSub.extTyp
  with type kind = StrobeSub.extKind
  with type binding = StrobeSub.extBinding
  with type env = StrobeSub.env)
  (Env : TYPESCRIPT_TYP_ENV
   with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type env = TypeScript.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
  : (TYPESCRIPT_SUBTYPING
     with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env) =
struct
  include TypeScript
  open TypeScript
  open ListExt

  let rec unfold_typdefs env typ =
    match typ with
    | TStrobe t -> embed_t (StrobeSub.unfold_typdefs env t)
    | TArrow _ -> typ

  let project t env =
    let free = free_ids t in
    let add_id_bindings set map = IdSet.fold (fun id acc ->
      try
        IdMap.add id (List.filter (fun b -> match b with BStrobe (Strobe.BTermTyp _) -> false | _ -> true)
                        (IdMap.find id env)) acc
      with Not_found -> acc) set map in
    let free_ids = add_id_bindings free IdMap.empty in
    let rec helper free_ids acc =
      if IdMap.cardinal free_ids = 0 then acc else
        let acc' = IdMap.fold IdMap.add free_ids acc in
        let free_ids' = IdMap.fold (fun id bs acc -> 
          let free_ids = List.fold_left (fun ids b -> match unwrap_b b with
            | BStrobe (Strobe.BTermTyp t) -> ids
            | BStrobe (Strobe.BTypDef(t, _))
            | BStrobe (Strobe.BTypBound(t, _))
            | BStrobe (Strobe.BLabelTyp t) -> 
              let free = TypeScript.free_ids (embed_t t) in
              IdSet.union ids free
            | BStrobe (Strobe.BEmbed _) -> ids
            | BStrobe (Strobe.BTyvar _) -> ids
            (* Your extra binding forms here *) )
            IdSet.empty bs in
          add_id_bindings free_ids acc) free_ids acc' in
        let free_ids' = IdMap.filter (fun id _ -> not (IdMap.mem id acc)) free_ids' in
        helper free_ids' acc' in
    helper free_ids IdMap.empty
  let project_typs t1 t2 (env : env) = IdMap.fold IdMap.add (project t1 env) (project t2 env)

  let rec subtype env s t =
     Strobe.trace "TS_subtype" (string_of_typ s ^ " <?: " ^ string_of_typ t) (fun x -> x) (fun () -> subtype' env s t)
  and subtype' (env : env) s t : bool = 
    match unwrap_t s, unwrap_t t with
      | TStrobe t1, TStrobe t2 -> 
        StrobeSub.subtype env t1 t2
      | TArrow (args1, None, ret1), TArrow (args2, None, ret2) ->
        if (List.length args1 > List.length args2) then false
        else
          let (right_args, _) = ListExt.split_at (List.length args1) args2 in
          let print_typ_list ts = List.iter (fun t ->
            Strobe.traceMsg "Argtyp: %s" (string_of_typ t)) ts in
          Strobe.traceMsg "rightargs:";
          print_typ_list right_args;
          Strobe.traceMsg "args2:";
          print_typ_list args2;
          Strobe.traceMsg "args1:";
          print_typ_list args1;
          (List.for_all2 (fun t1 t2 ->
            (subtype env t1 t2) || (subtype env t2 t1))
          args1 right_args) &&
          subtype env ret1 ret2
      (*
      | TArrow (args1, None, ret1), TArrow (args2, Some var2, ret2) ->
        if (List.length args1 < List.length args2) then (cache, false)
        else 
          let args2' = L.fill (List.length args1 - List.length args2) var2 args2 in
          (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2') (ret2::args1))
      | TArrow (args1, Some var1, ret1), TArrow (args2, None, ret2) ->
        if (List.length args1 > List.length args2) then (cache, false)
        else 
          let args1' = L.fill (List.length args2 - List.length args1) var1 args1 in
          (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2) (ret2::args1'))
      | TArrow (args1, Some var1, ret1), TArrow (args2, Some var2, ret2) ->
        if (List.length args1 > List.length args2) then
          let args2' = L.fill (List.length args1 - List.length args2) var2 args2 in
          (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2') (ret2::args1))
        else 
          let args1' = L.fill (List.length args2 - List.length args1) var1 args1 in
          (List.fold_left2 subtype_typ_list (cache, true) (ret1::args2) (ret2::args1'))
          *)
      | TStrobe (Strobe.TUnion (_, t1, t2)), (TArrow(args1, varargs1, ret1) as arr) ->
        StrobeSub.subtype env t1 (extract_t arr) &&
        StrobeSub.subtype env t2 (extract_t arr)
      | TArrow(args1, varargs1, ret1) as arr, TStrobe (Strobe.TUnion (_, t1, t2)) ->
        StrobeSub.subtype env (extract_t arr) t1 ||
        StrobeSub.subtype env (extract_t arr) t2
      | TArrow(args1, varargs1, ret1) as arr, TStrobe (Strobe.TInter (_, t1, t2)) ->
        StrobeSub.subtype env (extract_t arr) t1 &&
        StrobeSub.subtype env (extract_t arr) t2
      | TStrobe (Strobe.TInter (_, t1, t2)), (TArrow(args1, varargs1, ret1) as arr) ->
        StrobeSub.subtype env t1 (extract_t arr) ||
        StrobeSub.subtype env t2 (extract_t arr)
      | _ -> false

end
