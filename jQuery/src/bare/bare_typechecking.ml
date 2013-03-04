open Prelude
open Sig

module Make
  (Bare : Bare_sigs.BARE_MODULE)
  (Exp : Typedjs_syntax.EXP with module Typs = Bare.Strobe)
  (Env : Bare_sigs.BARE_TYP_ENV
   with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type env = Bare.env)
  (Sub : Bare_sigs.BARE_SUBTYPING
   with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)
  (Kind : Bare_sigs.BARE_KINDING
   with type typ = Bare.typ
  with type kind = Bare.kind
  with type binding = Bare.binding
  with type baseTyp = Bare.baseTyp
  with type baseKind = Bare.baseKind
  with type baseBinding = Bare.baseBinding
  with type env = Bare.env)
  (StrobeTC : Strobe_sigs.STROBE_TYPECHECKING
   with type typ = Bare.baseTyp
  with type kind = Bare.baseKind
  with type binding = Bare.baseBinding
  with type extTyp = Bare.typ
  with type extKind = Bare.kind
  with type extBinding = Bare.binding
  with type exp = Exp.exp
  with type env = Bare.env) =
struct
  type exp = Exp.exp
  include Bare
  open Exp
  open Bare


  let rec bind_forall_vars (env : env) (typ : typ) : env * typ = match typ with
    | TStrobe t -> let (env, t) = StrobeTC.bind_forall_vars env t in (env, embed_t t)
    (* Your extended types go here *)
    (* | typ -> (env, typ) *)

  let disable_flows () = StrobeTC.disable_flows () 
  (* need () because otherwise this is a value, not a function, and ML gets angry at that *)

  let rec forall_arrow (typ : typ) : ((id * binding) list * typ) option = match typ with
    | TStrobe s -> begin
      match StrobeTC.forall_arrow s with
        | None -> None
        | Some (ids, t) -> Some (ids, embed_t t)
      end
    (* Your extended types go here *)
    (* | _ -> None *)


  let rec assoc_sub env t1 t2 =
    let assocmap = typ_assoc env t1 t2 in
    let do_substitution p typ_vars t =
      let apply_typ_var tacc (tvar, binding) =
        try
          let print_binding x b = match b with
            | BStrobe (Strobe.BTypBound (b, _)) -> Strobe.traceMsg "Typ-bound %s %s" x (string_of_typ (embed_t b))
            | BStrobe (Strobe.BTermTyp (t)) -> Strobe.traceMsg "TermTyp-bound %s %s" x (string_of_typ (embed_t t))
            | _ -> Strobe.traceMsg "Weird bound"
          in
          IdMap.iter print_binding assocmap;
          typ_subst tvar 
            (match IdMap.find tvar assocmap, binding with
            | BStrobe (Strobe.BTermTyp t), BStrobe (Strobe.BTypBound(bindt, _)) -> 
              begin try
                if not (Sub.subtype env (embed_t t) (embed_t bindt))
                then begin
                  Strobe.typ_mismatch p
                    (Strobe.FixedString
                       (Printf.sprintf "%s is associated to %s, but this isn't a subtype of the bound %s"
                          tvar (string_of_typ (embed_t t)) (string_of_typ (embed_t bindt))));
                  embed_t t
                end else
                  embed_t t
              with
                e -> Strobe.traceMsg "Error during bound checking: %s" (Printexc.to_string e);
                raise e
              end
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

  let check (env : env) (default_typ : typ option) (exp : exp) (typ : typ) : unit = 
    match typ with
    | TStrobe t -> StrobeTC.check env default_typ exp t
    (* Your new types go here *)
    (* | _ -> Strobe.typ_mismatch (Exp.pos exp) (Strobe.FixedString "Bare.check NYI") *)

  let synth env default_typ exp : typ = 
    let ret = embed_t (StrobeTC.synth env default_typ exp) in 
    canonical_type ret

  let check_app env default_typ f args tfun =
    (* Checking your special arrow/function types against args (or re-checking
       f if you want) goes here *)
    raise (Strobe.Typ_error (pos f,
                             Strobe.FixedString "Bare: No special functions"))

  let typecheck env default_typ exp =
    let _ = synth env default_typ exp in
    ()

end
