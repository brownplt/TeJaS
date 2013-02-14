open Prelude
open Sig

module Make
  (TypeScript : TypeScript_sigs.TYPESCRIPT_MODULE)
  (Exp : Typedjs_syntax.EXP with module Typs = TypeScript.Strobe)
  (Env : TypeScript_sigs.TYPESCRIPT_TYP_ENV
   with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type env = TypeScript.env)
  (Sub : TypeScript_sigs.TYPESCRIPT_SUBTYPING
   with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env)
  (Kind : TypeScript_sigs.TYPESCRIPT_KINDING
   with type typ = TypeScript.typ
  with type kind = TypeScript.kind
  with type binding = TypeScript.binding
  with type baseTyp = TypeScript.baseTyp
  with type baseKind = TypeScript.baseKind
  with type baseBinding = TypeScript.baseBinding
  with type env = TypeScript.env)
  (StrobeTC : Strobe_sigs.STROBE_TYPECHECKING
   with type typ = TypeScript.baseTyp
  with type kind = TypeScript.baseKind
  with type binding = TypeScript.baseBinding
  with type extTyp = TypeScript.typ
  with type extKind = TypeScript.kind
  with type extBinding = TypeScript.binding
  with type exp = Exp.exp
  with type env = TypeScript.env) =
struct
  type exp = Exp.exp
  include TypeScript
  open Exp
  open TypeScript

  let trace msg success thunk exp = StrobeTC.trace msg success thunk exp

  let rec bind_forall_vars (env : env) (typ : typ) : env * typ = match typ with
    | TStrobe t -> let (env, t) = StrobeTC.bind_forall_vars env t in (env, embed_t t)
    | typ -> (env, typ)

  let disable_flows () = StrobeTC.disable_flows () 
  (* need () because otherwise this is a value, not a function, and ML gets angry at that *)

  let rec forall_arrow (typ : typ) : ((id * binding) list * typ) option = match typ with
    | TStrobe s -> begin
      match StrobeTC.forall_arrow s with
        | None -> None
        | Some (ids, t) -> Some (ids, embed_t t)
      end
    | _ -> None


  let rec assoc_sub env t1 t2 =
    let assocmap = typ_assoc env t1 t2 in
    let do_substitution p typ_vars t =
      let apply_typ_var tacc (tvar, binding) =
        try
          typ_subst tvar 
            (match IdMap.find tvar assocmap, binding with
            | BStrobe (Strobe.BTermTyp t), BStrobe (Strobe.BTypBound(bindt, _)) -> 
              if not (Sub.subtype env (embed_t t) (embed_t bindt))
              then begin
                Strobe.typ_mismatch p
                  (Strobe.FixedString
                     (Printf.sprintf "%s is associated to %s, but this isn't a subtype of the bound %s"
                        tvar (string_of_typ (embed_t t)) (string_of_typ (embed_t bindt))));
                embed_t t
              end else
                embed_t t
            | BStrobe (Strobe.BTermTyp _), _ ->
              failwith "impossible: somehow associated a type-id to a non-type bound"
            | _ -> failwith "impossible: never added anything but BTermTyps to the association map!"
            ) tacc
        with Not_found ->
          match binding with
          | BStrobe (Strobe.BTypBound(t, _)) ->
            raise (Strobe.Typ_error (p, Strobe.FixedString
              (Printf.sprintf "synth: could not instantiate typ_var %s under bound %s"
                 tvar (string_of_typ (embed_t t)))))
          | _ ->
	          raise (Strobe.Typ_error (p, Strobe.FixedString
	            (Printf.sprintf "synth: could not instantiate variable %s (with unknown bound??)"
                 tvar))) in
      let substituted = List.fold_left apply_typ_var t typ_vars in
      let resolved = canonical_type substituted in
      resolved in
    do_substitution

  let rec check (env : env) (default_typ : typ option) (exp : exp) (typ : typ) : unit =
    try trace "Check" (fun _ -> true) (fun exp -> check' env default_typ exp typ) exp
    (* typ_mismatch normally records the error and proceeds. If we're in a
       [with_typ_exns] context, it will re-raise the error. *)
    with Strobe.Typ_error (p, s) -> Strobe.typ_mismatch p s
      
  and check' (env : env) (default_typ : typ option) (exp : exp) (typ : typ) : unit = 
    match typ with
    | TStrobe t -> StrobeTC.check env default_typ exp t
    | _ -> Strobe.typ_mismatch (Exp.pos exp) (Strobe.FixedString "TypeScript.check NYI")

  let synth env default_typ exp : typ = 
    let ret = embed_t (StrobeTC.synth env default_typ exp) in 
    canonical_type ret

  let typecheck env default_typ exp =
    let _ = synth env default_typ exp in
    ()

end
