open Prelude
open Sig
open Strobe_sigs

module Make 
  (Strobe : STROBE_MODULE)
  (ExtKinding : EXT_KINDING
   with type typ = Strobe.extTyp
  with type kind = Strobe.extKind
  with type binding = Strobe.extBinding
  with type baseTyp = Strobe.typ
  with type baseKind = Strobe.kind
  with type baseBinding = Strobe.binding
  with type env = Strobe.env) =
struct
  include Strobe

  let valid_prims = ref (IdSetExt.from_list [ ])

  let list_prims () = IdSetExt.to_list !valid_prims

  let new_prim_typ (s : string) : unit =
    if IdSet.mem s !valid_prims then
      raise (Kind_error (s ^ " is already defined as a primitive type"))
    else (
      (* Printf.printf "Adding prim %s\n" s; *)
      valid_prims := IdSet.add s !valid_prims)

  let kind_mismatch typ calculated_kind expected_kind = 
    raise 
      (Kind_error 
         (sprintf "Expected kind %s, but got kind %s for type:\n%s"
            (string_of_kind expected_kind)
            (string_of_kind calculated_kind)
            (string_of_typ typ)))

  let trace prompt print thunk arg = thunk arg
    (* Strobe.trace prompt (print arg) (fun _ -> true) (fun () -> thunk arg) *)

  let rec kind_check (env : env) (recIds : id list) (typ : typ) : kind = 
    trace "KindCheck" Strobe.Pretty.simpl_typ (fun typ -> kind_check' env recIds typ) typ

  and kind_check' (env : env) (recIds : id list) (typ : typ) : kind =
    let bind_kind_id x k env = 
      let bs = try IdMap.find x env with Not_found -> [] in
      let bs = List.filter (fun b -> match Ext.extract_b b with BTyvar _ -> false | _ -> true) bs in
      IdMap.add x ((Ext.embed_b (BTyvar k))::bs) env in
    match typ with
    | TEmbed t -> Ext.extract_k (ExtKinding.kind_check env recIds t)
    | TTop
    | TBot
    | TRegex _ -> KStar
    | TUninit t -> begin match !t with
      | None -> kind_check env recIds (TPrim "Undef")
      | Some t -> kind_check env recIds t
    end
    | TPrim s -> 
      if IdSet.mem s !valid_prims then 
        KStar
      else
        raise (Kind_error (s ^ " is not a primitive type"))
    | TUnion (_, t1, t2)
    | TInter (_, t1, t2) ->
      begin match kind_check env recIds t1, kind_check env recIds t2 with
      | KStar, KStar -> KStar
      | k1, KStar -> kind_mismatch t1 k1 KStar
      | _, k2 -> kind_mismatch t2 k2 KStar
      end
    | TThis t -> kind_check env recIds t
    | TRef (_, t)
    | TSource (_, t)
    | TSink (_, t) ->
      begin match kind_check env recIds t with
      | KStar -> KStar
      | k -> kind_mismatch t k KStar
      end
    | TArrow (arg_typs, varargs, result_typ) ->
      let assert_kind t = match kind_check env recIds t with
        | KStar -> ()
        | k -> kind_mismatch t k KStar in
      List.iter assert_kind (result_typ :: arg_typs);
      (match varargs with None -> () | Some v -> assert_kind v);
      KStar
    | TObject o ->
      List.iter (assert_fld_kind env recIds) (fields o);
      KStar
    | TWith(t, flds) ->
      ignore (kind_check env recIds t);
      List.iter (assert_fld_kind env recIds) (fields flds);
      KStar
    | TId x -> 
      begin 
        try 
          let bs = IdMap.find x env in
          let b = List.find (fun b -> match b with BTyvar _ | BTypDef _ | BTypBound _ -> true | _ -> false) (List.map Ext.extract_b bs) in
          (match b with
          | BTyvar k -> k
          | BTypDef (_, k) -> k
          | BTypBound (_, k) -> k
          | _ -> failwith "impossible: List.find should only have returned BTyvars, BTypDefs or BTypBounds")
        with Not_found ->
          if (not (List.mem x recIds)) then
            let envText = FormatExt.to_string (fun e -> FormatExt.braces (Strobe.Pretty.env e)) env in
            let s = (sprintf "STROBE type variable %s is unbound in env %s" x envText) in
            (* Printf.eprintf "%s" s;  *)
            raise (Kind_error s)
          else KStar
      end
    | TForall (_, x, t1, t2) ->
      begin match kind_check env recIds t1, kind_check (bind_kind_id x KStar env) recIds t2 with
      | KStar, KStar -> KStar
      | k1, KStar -> kind_mismatch t1 k1 KStar
      | _, k2 -> kind_mismatch t2 k2 KStar
      end
    | TRec (_, x, t) ->
      begin match kind_check (bind_kind_id x KStar env) recIds t with
      | KStar -> KStar
      | k -> kind_mismatch t k KStar
      end
    | TLambda (_, args, t) ->
      let env' = fold_right (fun (x, k) env -> bind_kind_id x k env) args env in
      KArrow (List.map snd2 args, kind_check env' recIds t)
    | TFix (_, x, k, t) ->
      (* Printf.eprintf "Binding %s to %s for TFix\n" x (string_of_kind k); *)
      let k' = kind_check (bind_kind_id x k env) recIds t in
      if  k' = k then k
      else kind_mismatch typ k' k
    | TApp (t_op, t_args) ->
      begin 
        let check k_arg t_arg = 
          let k_actual = kind_check env recIds t_arg in
          if k_arg = k_actual then
            ()
          else 
            kind_mismatch t_arg k_actual k_arg in
        match t_op with
        | TPrim ("Constructing" as p)
        | TPrim ("Mutable" as p) 
        | TPrim ("Immutable" as p) ->
          begin 
            try List.iter2 check [KStar] t_args
            with Invalid_argument _ -> raise (Kind_error (p ^ "<> expects one argument"))
          end;
          KStar
        | _ -> match kind_check env recIds t_op with
          | KEmbed k -> raise (Kind_error (sprintf "operator got an extended kind %s"
                                             (ExtKinding.string_of_kind k)))
          | KArrow (k_args, k_result) ->
            begin 
              try
                List.iter2 check k_args t_args;
                k_result
              with Invalid_argument _ ->
                raise (Kind_error
                         (sprintf "operator expects %d args, given %d"
                            (List.length k_args) (List.length t_args)))
            end
          | KStar ->
            raise (Kind_error 
                     (sprintf "not a type operator:\n%s" (string_of_typ t_op)))
      end
        
  and assert_fld_kind (env : env) recIds (_, _, t) = match kind_check env recIds t with
    | KStar -> ()
    | k -> kind_mismatch t k KStar
end
