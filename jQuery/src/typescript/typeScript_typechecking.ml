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
  let traceMsg msg = StrobeTC.traceMsg msg

  let rec bind_forall_vars (env : env) (typ : typ) : env * typ = match typ with
    | TStrobe t -> let (env, t) = StrobeTC.bind_forall_vars env t in (env, embed_t t)
    | typ -> (env, typ)

  let disable_flows () = StrobeTC.disable_flows () 
  (* need () because otherwise this is a value, not a function, and ML gets angry at that *)

  let mapopt f s = match s with
    | None -> None
    | Some s' -> Some (f s')

  let shift_arrow typ = match typ with
    | TArrow (args, var, ret) ->
      TStrobe (Strobe.TArrow (map extract_t args, mapopt extract_t var, extract_t ret))
    | TStrobe _ -> typ

  let rec forall_arrow (typ : typ) : ((id * binding) list * typ) option = match typ with
    | TStrobe s -> begin
      match StrobeTC.forall_arrow s with
        | None -> None
        | Some (ids, t) -> Some (ids, embed_t t)
      end
    | TArrow _ as t ->
      Some ([], shift_arrow t)

  let rec assoc_sub env t1 t2 =
    traceMsg "In assoc_sub with %s %s" (string_of_typ t1)(string_of_typ t2);
    Env.print_env env Format.std_formatter;
    Format.pp_print_flush Format.std_formatter ();
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

  let expose_simpl_typ env typ = embed_t (Strobe.expose env (extract_t (simpl_typ env typ)))

  let rec check (env : env) (default_typ : typ option) (exp : exp) (typ : typ) : unit =
    try trace "Check" (fun _ -> true) (fun exp -> check' env default_typ exp typ) exp
    (* typ_mismatch normally records the error and proceeds. If we're in a
       [with_typ_exns] context, it will re-raise the error. *)
    with Strobe.Typ_error (p, s) -> Strobe.typ_mismatch p s
      
  and check' (env : env) (default_typ : typ option) (exp : exp) (typ : typ) : unit = 
    match exp with 
      | EFunc (p, args, func_info, body) -> 
        begin match expose_simpl_typ env typ with
          | TArrow (arg_typs, _, result_typ) ->
            if not (List.length arg_typs = List.length args) then
              Strobe.typ_mismatch p
                (Strobe.NumNum(sprintf "TSI: given %d argument names, but %d argument types", (List.length args), (List.length arg_typs)))
            else
              let bind_arg env x t = Env.bind_id x t env in
              let env = List.fold_left2 bind_arg env args arg_typs in
              let env = Env.clear_labels env in
              check env default_typ body result_typ
          | TStrobe t ->
            StrobeTC.check env default_typ exp t
        end
      | _ ->
        begin match typ with
          | TArrow _ ->
            failwith (sprintf "TSI: Got expression %s while checking arrow" (string_of_exp exp))
          | TStrobe t -> StrobeTC.check env default_typ exp t
        end

  let rec fill n a l = if n <= 0 then l else fill (n-1) a (List.append l [a])


  let rec synth env default_typ exp : typ = 
    trace "Synth" (fun _ -> true) (synth' env default_typ) exp

  and synth' env default_typ exp : typ = match exp with
    | EApp (p, f, args) -> 
      (* traceMsg "TS_synth: EApp with function %s | args %s" (string_of_exp f)
         (List.fold_left (fun acc a -> (acc ^ (string_of_exp a))) "" args); *)
      let ftyp = synth env default_typ f in
      let res_typ = check_app env default_typ f args ftyp in
      Strobe.traceMsg "TS_synth: EApp with function %s | args %s" (string_of_exp f)
         (List.fold_left (fun acc a -> (acc ^ (string_of_exp a))) "" args);
      Strobe.traceMsg "          Resulted in: %s" (string_of_typ res_typ);
      res_typ
    | _ ->
      Strobe.traceMsg "fallthrough in synth expr match: %s" (string_of_exp exp);
      let ret = canonical_type (embed_t (StrobeTC.synth env default_typ exp)) in
      Strobe.traceMsg "got synthed type: %s" (string_of_typ ret);
      ret

  and check_app env default_typ f args tfun =
      (* traceMsg "Checking EApp@%s with function type %s" (Pos.toString p) (string_of_typ tfun); *)
    let p = pos f in
    Strobe.traceMsg "TS_synth: Function type is %s" (string_of_typ tfun);
    match embed_t (Strobe.expose env (extract_t (simpl_typ env tfun))) with
      | TArrow (expected_typs, None, result_typ) -> 
        Strobe.traceMsg "TS_synth: Using an arrow type is %s" (string_of_typ tfun);
        let args = fill (List.length expected_typs - List.length args) 
          (EConst (p, JavaScript_syntax.CUndefined)) args in
        begin
          try List.iter2 (check env default_typ) args expected_typs
          with Invalid_argument "List.iter2" -> 
            Strobe.typ_mismatch p
              (Strobe.NumNum(sprintf "arity-mismatch:  %d args expected, but %d given",
                          (List.length expected_typs), (List.length args)))
        end;
        (* traceMsg "Strobe_synth EApp TArrow: result_typ is %s"(string_of_typ result_typ); *)
        result_typ
      | TArrow (expected_typs, Some vararg_typ, result_typ) -> 
        if (List.length expected_typs > List.length args) then
          let args = fill (List.length expected_typs - List.length args) 
            (EConst (p, JavaScript_syntax.CUndefined)) args in
          List.iter2 (check env default_typ) args expected_typs
        else begin
          let (req_args, var_args) = ListExt.split_at (List.length expected_typs) args in
          let req_args = fill (List.length expected_typs - List.length req_args)
            (EConst (p, JavaScript_syntax.CUndefined)) req_args in
          List.iter2 (check env default_typ) req_args expected_typs;
          List.iter (fun t -> check env default_typ t vararg_typ) var_args
        end;
        result_typ
      | TStrobe t ->
  (*          (Strobe.traceMsg "Fell through: %s" (string_of_typ (TStrobe t))) *)
        (* Strobe.traceMsg "fallthrough: %s" (string_of_exp exp); *)
        let ret = embed_t (StrobeTC.check_app env default_typ f args t) in 
        canonical_type ret 

  let typecheck env default_typ exp =
    let _ = synth env default_typ exp in
    ()

end
