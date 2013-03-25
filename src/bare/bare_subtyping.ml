open Prelude
open Sig
open Strobe_sigs
open Bare_sigs


module MakeActions
  (StrobeSub : STROBE_SUBTYPING)
  (Bare : BARE_MODULE
   with type baseTyp = StrobeSub.typ
  with type baseKind = StrobeSub.kind
  with type baseBinding = StrobeSub.binding
  with type typ = StrobeSub.extTyp
  with type kind = StrobeSub.extKind
  with type binding = StrobeSub.extBinding
  with type env = StrobeSub.env)
  (Env : BARE_TYP_ENV
   with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type env = Bare.env
  with type env_decl = Typedjs_writtyp.WritTyp.env_decl)
  : (BARE_SUBTYPING
     with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env) =
struct
  include Bare
  open Bare
  open ListExt

  let rec unfold_typdefs env typ =
    match typ with
    | TStrobe t -> embed_t (StrobeSub.unfold_typdefs env t)

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
              let free = Bare.free_ids (embed_t t) in
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

  let subtype env s t =
    match unwrap_t s, unwrap_t t with
      | TStrobe t1, TStrobe t2 -> 
        StrobeSub.subtype env t1 t2
      (* Your extended subtyping relation goes here, probably falls through *)
      (* | _ -> false *)

end
