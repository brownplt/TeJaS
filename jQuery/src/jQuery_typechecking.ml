open Prelude
open Sig

module Make
  (JQ : JQuery_sigs.JQUERY_MODULE)
  (Exp : Typedjs_syntax.EXP with module Typs = JQ.Strobe)
  (Env : JQuery_sigs.JQUERY_TYP_ENV
   with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type sigma = JQ.sigma
  with type binding = JQ.binding
  with type env = JQ.env)
  (Sub : JQuery_sigs.JQUERY_SUBTYPING
   with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type env = JQ.env)
  (Kind : JQuery_sigs.JQUERY_KINDING
   with type typ = JQ.typ
  with type kind = JQ.kind
  with type multiplicity = JQ.multiplicity
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type env = JQ.env)
  (StrobeTC : Strobe_sigs.STROBE_TYPECHECKING
   with type typ = JQ.baseTyp
  with type kind = JQ.baseKind
  with type binding = JQ.baseBinding
  with type extTyp = JQ.typ
  with type extKind = JQ.kind
  with type extBinding = JQ.binding
  with type exp = Exp.exp
  with type env = JQ.env) =
struct
  type exp = Exp.exp
  include JQ
  open Exp
  open JQ


  let trace msg success thunk exp = StrobeTC.trace msg success thunk exp
    
  let bind_sigma x s e = match s with
    | STyp t -> Env.bind_typ_id x t e
    | SMult m -> Env.bind_mult_id x m e

  let rec bind_forall_vars (env : env) (typ : typ) : env * typ = match typ with
    | TForall (n, x, s, t) -> bind_forall_vars (bind_sigma x s env) (apply_name n t)
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
    | TForall (_, x, b, typ') -> begin match forall_arrow typ' with
      | None -> None
      | Some (xs, typ) -> match b with
  | STyp t -> Some ((x, BStrobe (Strobe.BTypBound(extract_t t, Strobe.KStar))) :: xs, typ)
  | SMult m -> Some ((x, BMultBound (m, KMult (KStrobe Strobe.KStar))) :: xs, typ)
    end
    | _ -> None

  let rec assoc_sub env t1 t2 = assoc_sub' env t1 t2
    (* Strobe.trace "JQuery:Assoc_sub" (Printf.sprintf "assoc %s with %s" (string_of_typ t1) (string_of_typ t2)) (fun _ -> true) (fun () -> assoc_sub' env t1 t2) *)
  and assoc_sub' env t1 t2 =
    (* Strobe.traceMsg "associating %s with %s" (string_of_typ t1) (string_of_typ t2); *)
    (* let t1' = (Env.resolve_special_functions env !Env.senv (Env.expose_tdoms env (canonical_type t1))) in *)
    (* let t2' = (Env.resolve_special_functions env !Env.senv (Env.expose_tdoms env (canonical_type t2))) in *)
    let assocmap = typ_assoc env t1 t2 in
    (* Strobe.traceMsg "In assoc_sub, associations are:"; *)
    (* IdMap.iter (fun tvar b -> match b with *)
    (* | BMultBound (m, _) ->  *)
    (*   Strobe.traceMsg "  %s => %s" tvar (string_of_mult m) *)
    (* | BStrobe (Strobe.BTermTyp t) -> *)
    (*   Strobe.traceMsg "  %s => %s" tvar (string_of_typ (embed_t t)) *)
    (* | b -> Strobe.traceMsg "  %s => UNKNOWN BINDING!" tvar) assocmap; *)
    let do_substitution p typ_vars t =
      let apply_typ_var tacc (tvar, binding) =
        try
          sig_typ_subst tvar 
            (match IdMap.find tvar assocmap, binding with
            | BMultBound (m, _), BMultBound (bindm, _) -> 
              if not (Sub.subtype_mult true env m bindm)
              then begin
                Strobe.typ_mismatch p 
                  (Strobe.FixedString 
                     (Printf.sprintf "%s is associated to %s, but this isn't a sub-multiplicity of the bound %s"
                        tvar (string_of_mult m) (string_of_mult bindm)));
                SMult m
              end else
                SMult m
            | BStrobe (Strobe.BTermTyp t), BStrobe (Strobe.BTypBound(bindt, _)) -> 
              if not (Sub.subtype env (embed_t t) (embed_t bindt))
              then begin
                Strobe.typ_mismatch p
                  (Strobe.FixedString
                     (Printf.sprintf "%s is associated to %s, but this isn't a subtype of the bound %s"
                        tvar (string_of_typ (embed_t t)) (string_of_typ (embed_t bindt))));
                STyp (embed_t t)
              end else
                STyp (embed_t t)
            | BMultBound _, _
            | BStrobe (Strobe.BTermTyp _), _ ->
              failwith "impossible: somehow we associated a type-id to a multiplicity, or vice versa"
            | _ -> failwith "impossible: we never added anything but BMultBounds and BTermTyps to the association map!"
            ) tacc
        with Not_found ->
          match binding with
          | BMultBound (m, _) ->
            raise (Strobe.Typ_error (p, Strobe.FixedString
              (Printf.sprintf "synth: could not instantiate mult_var %s under bound %s"
                 tvar (string_of_mult m))))
          | BStrobe (Strobe.BTypBound(t, _)) ->
            raise (Strobe.Typ_error (p, Strobe.FixedString
              (Printf.sprintf "synth: could not instantiate typ_var %s under bound %s"
                 tvar (string_of_typ (embed_t t)))))
          | _ ->
	          raise (Strobe.Typ_error (p, Strobe.FixedString
	            (Printf.sprintf "synth: could not instantiate variable %s (with unknown bound??)"
                 tvar))) in
      let substituted = List.fold_left apply_typ_var t typ_vars in
      (* TODO(liam): Test to see if resolved really needs to be called here *)
      let resolved = Env.resolve_special_functions env !Env.senv (Sub.subtype_mult true)
        (canonical_type substituted) in
      (* Strobe.traceMsg "In do_substitution: original typ is %s" (string_of_typ t); *)
      (* Strobe.traceMsg "In do_substitution: subst'd is %s" (string_of_typ substituted); *)
      (* Strobe.traceMsg "In do_substitution: resolved typ is %s" (string_of_typ resolved) ;*)
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
    | _ -> Strobe.typ_mismatch (Exp.pos exp) (Strobe.FixedString "JQuery.check NYI")

  and synth (env : env) (default_typ : typ option) (exp : exp) : typ = 
    (* Strobe.traceMsg "Attempting to synth %s"(string_of_exp exp); *)
    (* let res = synth' env default_typ exp in *)
    (* Strobe.traceMsg "Result of jQuery_synth is: %s"(string_of_typ res); *)
    (* res *)
    trace "JQuery:Synth" (fun _ -> true) (synth' env default_typ) exp
  and synth' env default_typ exp : typ = 
    let ret = match exp with
    | ETypApp (p, e, u) ->
      begin match embed_t (Strobe.expose env (extract_t (simpl_typ env (synth env default_typ e)))) with
      | TForall (n, x, STyp s, t) ->
        if Sub.subtype env u s then
          apply_name n (typ_subst x u t)
        else 
          begin
            Strobe.typ_mismatch p
              (Strobe.TypTyp((fun t1 t2 -> sprintf "type-argument %s is not a subtype of the bound %s"
                (string_of_typ (embed_t t1)) (string_of_typ (embed_t t2))), 
                             (extract_t u), (extract_t s)));
            typ_subst x s t (* Warning: produces possibily spurious errors *)
          end
      | TStrobe t ->
        embed_t (StrobeTC.synth env default_typ exp)
      | t ->
        Strobe.traceMsg "In ETypApp, and things went badly wrong with %s\n" (string_of_typ t);
        raise
          (Strobe.Typ_error (p, Strobe.TypTyp((fun t1 t2 -> 
            sprintf "expected forall-type in type application, got:\n%s\ntype argument is:\n%s"
              (string_of_typ (embed_t t1)) (string_of_typ (embed_t t2))), 
                                              (extract_t t), (extract_t u))))
      end      
    | _ ->
      embed_t (StrobeTC.synth env default_typ exp)
    in 
    Env.resolve_special_functions env !Env.senv (Sub.subtype_mult true) (canonical_type ret)

  let typecheck env default_typ exp =
    let _ = synth env default_typ exp in
    ()

end
