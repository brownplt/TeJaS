open Prelude
open ListExt
open JQuery_syntax
open TypImpl
open JQuery_subtyping
open JQuery_env
open Exp


let simpl_print e = match e with
  | EConst(p, _) -> "EConst " ^ (Pos.toString p)
  | EAssertTyp(p, _, _) -> "EAssertTyp " ^ (Pos.toString p)
  | EId(p, x) -> "EId " ^ x ^ " " ^ (Pos.toString p)
  | EApp(p, _, _) -> "EApp " ^ (Pos.toString p)
  | EFunc(p, _, _, _) -> "EFunc " ^ (Pos.toString p)
  | ELet (p, _, _, _) -> "ELet " ^ (Pos.toString p)
  | ERec (p, _, _) -> "ERec " ^ (Pos.toString p)
  | ESeq (p, _, _) -> "ESeq " ^ (Pos.toString p)
  | ECheat(p, _, _) -> "ECheat " ^ (Pos.toString p)

let depth = ref 0
let trace (msg : string) (thunk : exp -> 'a) (exp : exp)  = thunk exp
    (* Printf.eprintf "%s-->%s %s\n" (String.make (!depth) ' ') msg (simpl_print exp); *)
    (* depth := !depth + 1; *)
    (* try *)
    (*   let ret = thunk exp in *)
    (*   depth := !depth - 1; *)
    (*   Printf.eprintf "%s<--%s %s\n" (String.make (!depth) ' ') msg (simpl_print exp); *)
    (*   ret *)
    (* with e -> *)
    (*   depth := !depth - 1; *)
    (*   Printf.eprintf "%s<X-%s %s\n" (String.make (!depth) ' ') msg (simpl_print exp); *)
    (*   raise e *)

let rec check (env : env) (default_typ : TypImpl.typ option) (exp : exp) (typ : TypImpl.typ) : unit =
  try trace "Check" (fun exp -> check' env default_typ exp typ) exp
  (* typ_mismatch normally records the error and proceeds. If we're in a
     [with_typ_exns] context, it will re-raise the error. *)
  with Typ_error (p, s) -> typ_mismatch p s
    
and check' (env : env) (default_typ : TypImpl.typ option) (exp : exp) (typ : TypImpl.typ) : unit = 
  (* Printf.eprintf "Check': checking %s : %s\n" (string_of_exp exp) (string_of_typ typ); *)
  match exp with
  | EFunc(p, name, args, body) -> 
    begin match typ with
    | TInter(_, t1, t2) -> 
      (try (with_typ_exns (fun () -> check env default_typ exp t1))
       with Typ_error (p, e) -> 
         typ_mismatch p
           (sprintf "Expected function to have type %s, but it failed to have (first-part) type %s because %s"
              (string_of_typ typ) (string_of_typ t1) e));
      (try (with_typ_exns (fun () -> check env default_typ exp t2))
       with Typ_error (p, e) -> 
         typ_mismatch p
           (sprintf "Expected function to have type %s, but it failed to have (second-part) type %s because %s"
              (string_of_typ typ) (string_of_typ t2) e))
    | TUnion(_, t1, t2) ->
      (try (with_typ_exns (fun () -> check env default_typ exp t1))
       with Typ_error _ -> check env default_typ exp t2)
    | TArrow(_, arg_typs, None, ret) ->
      if not (List.length arg_typs = List.length args) then
        typ_mismatch p
          (sprintf "given %d argument names, but %d argument types" (List.length args) (List.length arg_typs))
      else
        let bind_arg env x t = bind_id x t env in
        let env = List.fold_left2 bind_arg env args arg_typs in
        check env default_typ body ret
    | TArrow (_, arg_typs, Some vararg_typ, result_typ) ->
      let bind_arg env x t = bind_id x t env in
      let bind_vararg env x = bind_arg env x vararg_typ in
      let (req_args, var_args) = ListExt.split_at (List.length arg_typs) args in
      let env = List.fold_left2 bind_arg env req_args arg_typs in
      let env = List.fold_left bind_vararg env var_args in
      check env default_typ body result_typ
    | t -> 
        raise (Typ_error (p, (sprintf "invalid type annotation on a function: %s" (string_of_typ t))))
    end
  | _ ->
    (* Printf.eprintf "Check': Synthing type for expression\n"; *)
    let synth_typ = synth env default_typ exp in
    (* Printf.printf "Checking %s <?: %s\n" (string_of_typ synth_typ) (string_of_typ (expose_simpl_typ env typ)); *)
    if not (subtype_typ ((* lax *)true) env synth_typ typ) then begin
      (* Printf.printf "failed.\n"; *)
      typ_mismatch (Exp.pos exp)
        (sprintf "%%expected %s to have type %s, got %s" 
           (string_of_exp exp) (string_of_typ typ) (string_of_typ synth_typ))
    end (* else *)
      (* Printf.printf "Checking finished.\n" *)

and synth (env : env) (default_typ : typ option) (exp : exp) : typ = 
  trace "Synth" (synth' env default_typ) exp
and synth' env default_typ exp : typ =
  (* Printf.eprintf "*Synthing type for %s\n" (string_of_exp exp); *)
  match exp with
  | EConst (p, _) -> TId "String" (* for now *)
  | EAssertTyp(p, t, e) ->
    (* Printf.eprintf "Synth: AssertTyp that %s has type %s\n" (string_of_exp e) (string_of_typ t); *)
    (* Printf.eprintf "%s\n" (string_of_bool (subtype env (synth env default_typ e) t)); *)
    let _ = JQuery_kinding.kind_check_typ env [] t in
    let _ = check env default_typ e t in
    t
  | EId (p, x) -> begin
    try 
      lookup_id x env
    with Not_found -> match default_typ with
    | None -> raise (Typ_error (p, (sprintf "%s is not defined" x))) (* severe *)
    | Some t -> 
      Printf.eprintf "Warning: Unbound identifier %s at %s\n" x (Pos.toString p);
      Printf.eprintf "Currently bound identifiers are:\n";
      IdMap.iter (fun id b -> match b with BTermTyp _ -> Printf.eprintf "%s, " id | _ -> ()) env;
      Printf.eprintf "\n";
      t (* Should probably warn about undefined identifier here *)
  end
  | EApp(p, f, xs) -> 
    let rec check_app tfun =
      begin match tfun with
      | TArrow(_, args, None, ret) -> 
        let xs = fill (List.length args - List.length xs) (EConst (p, "placeholder")) xs in
        begin try List.iter2 (check env default_typ) xs args
          with Invalid_argument _ -> 
            typ_mismatch p
              (sprintf "arity-mismatch: %d args expected, but %d given" (List.length args) (List.length xs))
        end;
        ret
      | TArrow (_, args, Some var, ret) -> 
        if (List.length args > List.length args) then
          let xs = fill (List.length args - List.length args) (EConst (p, "placeholder")) xs in
          List.iter2 (check env default_typ) xs args
        else begin
          let (req_xs, var_xs) = ListExt.split_at (List.length args) xs in
          let req_xs = fill (List.length args - List.length req_xs) (EConst (p, "placeholder")) req_xs in
          List.iter2 (check env default_typ) req_xs args;
          List.iter (fun t -> check env default_typ t var) var_xs
        end;
        ret
      | TInter(_, t1, t2) ->
        (with_typ_exns (fun () -> try check_app t1 with Typ_error _ -> check_app t2))
      | TUnion (n, t1, t2) ->
        let typ_or_err t = with_typ_exns (fun () -> try Some (check_app t) with Typ_error _ -> None) in
        let r1 = typ_or_err t1 in
        let r2 = typ_or_err t2 in
        (match r1, r2 with
        | Some r, None
        | None, Some r -> apply_name n r
        | _ -> raise (Typ_error (p, "synth: Ambiguous union of functions")))
      | not_func_typ -> 
          (* even in an intersection, this should count as a genuine error *)
        raise (Typ_error (p,
                          sprintf "expected function, got %s" (string_of_typ not_func_typ)))
      end in 
    (* Printf.eprintf "Synth EApp: Checking function body\n"; *)
    check_app (synth env default_typ f)
  | ECheat(p, t, _) -> t
  | EFunc _ -> TArrow(None, [], Some TBot, TTop) (* TODO *)
  | ELet (_, x, e1, e2) -> synth (bind_id x (synth env default_typ e1) env) default_typ e2
  | ESeq (_, e1, e2) -> begin match synth env default_typ e1 with
      TBot -> (* e1 will not return; no need to typecheck e2 *)
        TBot
      | _ -> synth env default_typ e2
  end
  | ERec (p, binds, body) -> 
    (* No kinding check here, but it simply copies the type from the function.
       Let it work. (Actual reason: no position available) *)
    let f env (x, t, e) = bind_id x t env in
    let env = fold_left f env binds in
    let tc_bind (x, t, e) = check env default_typ e t in
    List.iter tc_bind binds;
    synth env default_typ body 
