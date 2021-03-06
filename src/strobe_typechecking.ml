open Prelude
open Sig

module Make
  (Typ : Strobe_sigs.STROBE_MODULE)
  (Exp : Typedjs_syntax.EXP with module Typs = Typ)
  (Env : TYP_ENV
   with type typ = Typ.extTyp
  with type kind = Typ.extKind
  with type binding = Typ.extBinding
  with type env = Typ.env)
  (Sub : Strobe_sigs.STROBE_SUBTYPING
   with type typ = Typ.typ
  with type kind = Typ.kind
  with type binding = Typ.binding
  with type extTyp = Typ.extTyp
  with type extKind = Typ.extKind
  with type extBinding = Typ.extBinding
  with type pat = Typ.pat
  with type obj_typ = Typ.obj_typ
  with type presence = Typ.presence
  with type env = Typ.env)
  (Kind : EXT_KINDING
   with type baseTyp = Typ.typ
  with type baseKind = Typ.kind
  with type baseBinding = Typ.binding
  with type typ = Typ.extTyp
  with type kind = Typ.extKind
  with type binding = Typ.extBinding
  with type env = Typ.env)
  (Semicfa : SEMICFA
   with type env = Typ.env
  with type exp = Exp.exp)
  (Static : Typedjs_syntax.STATIC
   with type env = Env.env
   with type typ = Env.typ)
  (ExtTC : EXT_TYPECHECKING
   with type typ = Typ.extTyp
  with type kind = Typ.extKind
  with type binding = Typ.extBinding
  with type baseTyp = Typ.typ
  with type baseKind = Typ.kind
  with type baseBinding = Typ.binding
  with type exp = Exp.exp
  with type env = Typ.env) =
struct
  type exp = Exp.exp
  include Typ
  open Exp
  open Typ

  let consumed_owned_vars  = ref IdSet.empty

  let array_idx_pat = 
    Pat.parse Lexing.dummy_pos
      "(([0-9])*|(\"+Infinity\"|(\"-Infinity\"|\"NaN\")))"


  let mk_array_typ p env elt_typ =
    TApp (TId "Array", [elt_typ])

  let is_flows_enabled = ref true

  let disable_flows () = is_flows_enabled := false

  let rec skip n l = if n == 0 then l else (skip (n-1) (List.tl l))
  let rec fill n a l = if n <= 0 then l else fill (n-1) a (List.append l [a])

  let un_null t = match t with
    | TUnion (n, TPrim "Undef", t')
    | TUnion (n, t', TPrim "Undef")
    | TUnion (n, TPrim "Null", t')
    | TUnion (n, t', TPrim "Null") -> apply_name n t'
    | _ -> t

  let check_kind p env (typ : typ) : typ =
    try
      match Ext.extract_k (Kind.kind_check env [] (Ext.embed_t typ)) with
      | KStar 
      | KEmbed _ -> typ
      | k ->
        raise (Sub.Typ_error  (p, Sub.TypKind((fun t k -> sprintf "type %s has kind %s; expected *"
          (string_of_typ t) (string_of_kind k)), typ, k)))
    with
    | Typ.Kind_error msg ->
      traceMsg "Couldn't check type for %s" (string_of_typ typ);
      raise (Typ.Kind_error (Pos.toString p ^ ": " ^ msg))
         
  let expose_simpl_typ env typ = expose env (simpl_typ env typ)

  let rec bind_forall_vars (env : env) (typ : Typ.typ) : env * Typ.typ = match typ with
    | TForall (n, x, s, t) -> bind_forall_vars (Env.bind_typ_id x (Ext.embed_t s) env) (apply_name n t)
    | TEmbed t -> let (env, t) = ExtTC.bind_forall_vars env t in (env, Ext.extract_t t)
    | typ -> (env, typ)


  let combine n m = if n = None then m else n
  let extract_ref msg p env t = 
    let rec helper t n = match expose_simpl_typ env t with
      | TPrim _  -> None
      | TRegex _ -> Some t
      | TRef _ as t -> Some (apply_name n t)
      | TSource _ as t -> Some (apply_name n t)
      | TSink _ as t -> Some (apply_name n t)
      | TRec(n', _, _) as t -> helper (simpl_typ env t) (combine n' n)
      | TThis t -> helper t n
      | TUnion (n', t1, t2) -> 
        let r1 = helper t1 (combine n' n) in
        let r2 = helper t2 (combine n' n) in
        (match r1, r2 with
        | Some r, None
        | None, Some r
        | Some r, Some (TRegex _)
        | Some (TRegex _), Some r -> Some (apply_name (combine n' n) r)
        | _ -> None) 
      | TInter (n', t1, t2) -> 
        let r1 = helper t1 (combine n' n) in
        let r2 = helper t2 (combine n' n) in
        (match r1, r2 with
        | Some r, None
        | None, Some r
        | Some r, Some (TRegex _)
        | Some (TRegex _), Some r -> Some (apply_name (combine n' n) r)
        | _ -> None)
      | TForall _ -> Some (apply_name n t) (* BSL : This seems incomplete; extract_ref won't descend under a Forall *)
      | _ -> (printf "%s: Got to %s\n" msg (string_of_typ t)); None in
    match helper t None with
    | Some t -> t
    | None -> raise (Sub.Typ_error (p, Sub.StringTyp((fun s t -> sprintf "%s: Ambiguous ref type for type %s"
      s (string_of_typ t)), msg, t)))

  let extract_arrow p env t = 
    let rec helper t = match expose_simpl_typ env t with
      | TArrow _ as t -> Some t
      | TUnion (_, t1, t2) -> 
        let r1 = helper t1 in
        let r2 = helper t2 in
        (match r1, r2 with
        | Some r, None
        | None, Some r -> Some r
        | _ -> None) 
      | TInter(n, t1, t2) ->
        let r1 = helper t1 in
        let r2 = helper t2 in
        (match r1, r2 with
        | Some r, None
        | None, Some r -> Some r
        | Some r1, Some r2 -> Some (TInter(n, r1, r2))
        | _ -> None) 
      | TForall _ -> Some t (* BSL : This seems incomplete; extract_arrow won't descend under a Forall *)
      | TEmbed t' -> begin
        match ExtTC.forall_arrow t' with
        | Some _ -> Some t
        | None -> None
      end
      | _ -> None in
    match helper t with
    | Some t -> t
    | None -> raise (Sub.Typ_error (p, Sub.FixedString ("Ambiguous arrow type for " ^ (string_of_typ t))))


  let simpl_print e = match e with
    | EConst(p, _) -> "EConst " ^ (Pos.toString p)
    | EBot(p) -> "EBot " ^ (Pos.toString p)
    | EAssertTyp(p, _, _) -> "EAssertTyp " ^ (Pos.toString p)
    | EArray(p, _) -> "EArray " ^ (Pos.toString p)
    | EObject(p, _) -> "EObject " ^ (Pos.toString p)
    | EId(p, x) -> "EId " ^ x ^ " " ^ (Pos.toString p)
    | EBracket(p, _, _) -> "EBracket " ^ (Pos.toString p)
    | EUpdate(p, _, _, _) -> "EUpdate " ^ (Pos.toString p)
    | EPrefixOp(p, x, _) -> "EPrefixOp " ^ x ^ " " ^ (Pos.toString p)
    | EInfixOp(p, x, _, _) -> "EInfixOp " ^ x ^ " " ^ (Pos.toString p)
    | EIf(p, _, _, _) -> "EIf " ^ (Pos.toString p)
    | EApp(p, _, _) -> "EApp " ^ (Pos.toString p)
    | EFunc(p, _, _, _) -> "EFunc " ^ (Pos.toString p)
    | ELet(p, x, _, _) -> "ELet " ^ x ^ " " ^ (Pos.toString p)
    | ERec(p, _, _) -> "ERec " ^ (Pos.toString p)
    | ESeq(p, _, _) -> "ESeq " ^ (Pos.toString p)
    | ELabel(p, _, _) -> "ELabel " ^ (Pos.toString p)
    | EBreak(p, _, _) -> "EBreak " ^ (Pos.toString p)
    | ETryCatch(p, _, _, _) -> "ETryCatch " ^ (Pos.toString p)
    | ETryFinally(p, _, _) -> "ETryFinally " ^ (Pos.toString p)
    | EThrow(p, _) -> "EThrow " ^ (Pos.toString p)
    | ETypecast(p, _, _) -> "ETypecast " ^ (Pos.toString p)
    | ERef (p, _, _) -> "ERef " ^ (Pos.toString p)
    | EDeref(p, _) -> "EDeref " ^ (Pos.toString p)
    | ESetRef(p, _, _) -> "ESetRef " ^ (Pos.toString p)
    | ESubsumption(p, _, _) -> "ESubsumption " ^ (Pos.toString p)
    | EDowncast(p, _, _) -> "EDowncast " ^ (Pos.toString p)
    | ETypAbs(p, _, _, _) -> "ETypAbs " ^ (Pos.toString p)
    | ETypApp(p, _, _) -> "ETypApp " ^ (Pos.toString p)
    | ECheat(p, _, _) -> "ECheat " ^ (Pos.toString p)
    | EParen(p, _) -> "EParen " ^ (Pos.toString p)


  let rec usesThis exp = match exp with
    | EConst (p, c) -> false
    | EBot p -> false
    | EAssertTyp (p, t, e) -> usesThis e
    | EArray (p, es) -> List.exists usesThis es
    | EObject (p, flds) -> List.exists usesThis (map snd flds)
    | EId (p, x) -> x = "this"
    | EBracket (p, e1, e2) -> usesThis e1 || usesThis e2
    | EUpdate (p, e1, e2, e3) -> usesThis e1 || usesThis e2 || usesThis e3
    | EPrefixOp (p, op, e) -> usesThis e
    | EInfixOp (p, op, e1, e2) -> usesThis e1 || usesThis e2
    | EIf (p, e1, e2, e3) -> usesThis e1 || usesThis e2 || usesThis e3
    | EApp (p, e, es) -> List.exists usesThis (e::es)
    | EFunc (p, xs, fi, e) -> usesThis e
    | ELet (p, x, e1, e2) -> usesThis e1 || usesThis e2
    | ERec (p, binds, body) -> usesThis body
    | ESeq (p, e1, e2) -> usesThis e1 || usesThis e2
    | ELabel (p, x,  e) -> usesThis e
    | EBreak (p, x, e) -> usesThis e
    | ETryCatch (p, e1, x, e2) -> usesThis e1 || usesThis e2
    | ETryFinally (p, e1, e2) -> usesThis e1 || usesThis e2
    | EThrow (p, e) -> usesThis e
    | ETypecast (p, s, e) -> usesThis e
    | ERef (p, k, e) -> usesThis e
    | EDeref (p, e) -> usesThis e
    | ESetRef (p, e1, e2) -> usesThis e1 || usesThis e2
    | ESubsumption (p, t, e) -> usesThis e
    | EDowncast (p, t, e) -> usesThis e
    | ETypAbs (p, x, t, e) -> usesThis e
    | ETypApp (p, e, t) -> usesThis e
    | ECheat (p, t, e) -> usesThis e
    | EParen (p, e) -> usesThis e



  let rec forall_arrow (typ : typ) : ((id * extBinding) list * typ) option = match typ with
    | TEmbed t -> begin
      match ExtTC.forall_arrow t with
      | None -> None
      | Some (ids, t) -> Some (ids, Ext.extract_t t)
    end
    | TArrow _ -> Some ([], typ)
    | TForall (_, x, b, typ') -> begin match forall_arrow typ' with
      | None -> None
      | Some (xs, t) -> Some ((x, Ext.embed_b (BTypBound(b, KStar))) :: xs, t)
    end
    | TRec (_, x, t) -> forall_arrow (typ_subst x typ t)
    | _ -> None


  let trace (msg : string) (success : 'a -> bool) (thunk : exp -> 'a) (exp : exp) = (* thunk exp  *)
   Typ.trace msg (simpl_print exp) success (fun () -> thunk exp) 

  let rec check (env : env) (default_typ : Typ.extTyp option) (exp : exp) (typ : Typ.typ) : unit =
    try trace "Check" (fun _ -> true) (fun exp -> check' env default_typ exp typ) exp
    (* typ_mismatch normally records the error and proceeds. If we're in a
       [with_typ_exns] context, it will re-raise the error. *)
    with Sub.Typ_error (p, s) -> Sub.typ_mismatch p s
      
  and check' (env : env) (default_typ : Typ.extTyp option) (exp : exp) (typ : Typ.typ) : unit = 
    (* traceMsg "Check': checking %s : %s" (string_of_exp exp) (string_of_typ typ); *)
    match exp with
    | ELabel (p, lbl, e) ->
      (* traceMsg "Check': Binding label %s in expression %s" lbl (string_of_exp e); *)
      let s = Ext.extract_t (ExtTC.synth (Env.bind_lbl lbl (Ext.embed_t typ) env) default_typ e) in
      if not (Sub.subtype env s (expose env typ)) then
        Sub.typ_mismatch p (Sub.TypTyp((fun t1 t2 -> sprintf "label has type %s, but body returns %s"
          (string_of_typ t1) (string_of_typ t2)), typ, s))
    | ELet (_, x, e1, e2) -> 
      check (Env.bind_id x (ExtTC.synth env default_typ e1) env) default_typ e2 typ
    | ECheat (p, t, (EFunc(pf, args, func_info, body) as f)) -> 
      let t = Ext.extract_t t in
      (* traceMsg "Cheating to %s" (string_of_typ (replace_name None t)); *)
      let simpl_t = expose_simpl_typ env t in
      (* traceMsg "Exposed typ is %s" (string_of_typ (replace_name None simpl_t)); *)
      check env default_typ f simpl_t
    | EFunc (p, args, func_info, body) -> 
      let misowned_vars = IdSet.inter !consumed_owned_vars 
        func_info.func_owned in
      consumed_owned_vars := IdSet.union !consumed_owned_vars
        func_info.func_owned;
      let owned_vars = IdSet.diff func_info.func_owned misowned_vars in
      begin match bind_forall_vars env (extract_arrow p env (expose_simpl_typ env (check_kind p env (expose_simpl_typ env typ)))) with
      | (env, (TInter(_, t1, t2) as t)) ->
        (try
           Sub.with_typ_exns (fun () -> check env default_typ exp t1)
         with Sub.Typ_error (p, e) -> Sub.typ_mismatch p
           (Sub.TypTyp((fun t1 t2 ->
             sprintf "Expected function to have type %s, but it failed to have (first-part) type %s because %s"
               (string_of_typ t1) (string_of_typ t2) (Sub.typ_error_details_to_string e)),
                   t, t1)));
        (try
           Sub.with_typ_exns (fun () -> check env default_typ exp t2)
         with Sub.Typ_error (p, e) -> Sub.typ_mismatch p
           (Sub.TypTyp((fun t1 t2 ->
             sprintf "Expected function to have type %s, but it failed to have (second-part) type %s because %s"
               (string_of_typ t1) (string_of_typ t2) (Sub.typ_error_details_to_string e)),
                   t, t1)))
      | (env, TArrow (arg_typs, _, result_typ)) ->
        if not (List.length arg_typs = List.length args) then
          let print_arg_list args = List.iter (fun a -> traceMsg "Arg: %s" a) args
          in
          let print_typ_list args = List.iter (fun a -> traceMsg "Arg: %s" (string_of_typ a)) args
          in
          traceMsg "arrow args:";
          print_arg_list args;
          traceMsg "arrow typs:";
          print_typ_list arg_typs;
          Sub.typ_mismatch p
            (Sub.NumNum(sprintf "given %d argument names, but %d argument types", (List.length args), (List.length arg_typs)))
        else
          let bind_arg env x t = Env.bind_id x (Ext.embed_t t) env in
          let env = List.fold_left2 bind_arg env args arg_typs in
          let env = Env.clear_labels env in
          let body = 
            if !is_flows_enabled then
              Semicfa.semicfa owned_vars env body 
            else 
              body in
          (* traceMsg "Owned = %s\n" (FormatExt.to_string
             (IdSetExt.p_set FormatExt.text) func_info.func_owned);
             traceMsg "Rewritten to:\n%s\n\n\n" (string_of_exp body);  *)
          check env default_typ body result_typ
      | (env, TEmbed t) -> ExtTC.check env default_typ exp t
      | _, t -> 
        raise (Sub.Typ_error (p, Sub.Typ((fun t -> sprintf "invalid type annotation on a function: %s" (string_of_typ t)), t)))
      end
    | ERef (p, ref_kind, e) -> 
      begin match ref_kind, extract_ref "ERef" p env (check_kind p env (expose_simpl_typ env typ)) with
      | RefCell, TSource(_, t) -> 
        begin
          try (Sub.with_typ_exns (fun () -> check env default_typ e t))
          with Sub.Typ_error(p, exn) ->
            (* traceMsg "Couldn't check ref as source directly; trying synthing: %s" *)
            (*   (Sub.typ_error_details_to_string exn); *)
            let e_typ = Ext.extract_t (ExtTC.synth env default_typ e) in
            if not (Sub.subtype env e_typ t) 
            then Sub.typ_mismatch p (Sub.TypTyp ((fun t1 t2 -> sprintf "Expected TRef(%s), got TSource(%s)" 
              (string_of_typ t1) (string_of_typ t2)), t, e_typ))
        end
      | SinkCell, TRef (_, t) ->
        begin
          try (Sub.with_typ_exns (fun () -> check env default_typ e t))
          with Sub.Typ_error _ ->
            (* traceMsg "Couldn't check sink as ref directly; trying synthing"; *)
            let e_typ = Ext.extract_t (ExtTC.synth env default_typ e) in
            if not (Sub.subtype env t e_typ) 
            then Sub.typ_mismatch p (Sub.TypTyp ((fun t1 t2 -> sprintf "Expected TSink(%s), got TRef(%s)" 
              (string_of_typ t1) (string_of_typ t2)), t, e_typ))
        end
      | SourceCell, TSource (_, t)
      | RefCell, TRef (_, t)
      | SinkCell, TSink (_, t) -> check env default_typ e t
      | SourceCell, TRef _ -> Sub.typ_mismatch p (Sub.FixedString "Expected a SourceCell, got a TRef")
      | SourceCell, TSink _ -> Sub.typ_mismatch p (Sub.FixedString "Expected a SourceCell, got a TSink")
      | SinkCell, TSource _ -> Sub.typ_mismatch p (Sub.FixedString "Expected a SinkCell, got a TSource")
      | RefCell, TSink _ -> Sub.typ_mismatch p (Sub.FixedString "Expected a RefCell, got a TSink")
      | _, t  -> Sub.typ_mismatch p (* TODO(arjun): error msg *)
        (Sub.TypTyp((fun t1 t2 -> sprintf "!!for expression %s, expected %s, got %s" (string_of_exp e)
          (string_of_typ t1) (string_of_typ t2)), t, Ext.extract_t (ExtTC.synth env default_typ e)))
      end
    | EArray (p, es) ->
      let expect_elt_typ = 
        Sub.simpl_lookup p env (un_null (expose_simpl_typ env typ)) array_idx_pat in
      let expect_array_typ = mk_array_typ p env expect_elt_typ in
      (if not (Sub.subtype env (TRef (None, typ)) expect_array_typ) then
          Sub.typ_mismatch p 
            (Sub.TypTyp((fun t1 t2 -> sprintf "check: expected Array<%s>, got %s" (string_of_typ t1) (string_of_typ t2)), expect_elt_typ, (TRef (None, typ)))));
      List.iter (fun e -> check env default_typ e expect_elt_typ) es 
    | EParen (_, e) -> check env default_typ e typ
    | EObject (p, fields) -> begin match expose_simpl_typ env typ with
      | TObject _ as t -> 
        let absPat = Pat.negate (Pat.unions (List.map (fun (f, _) -> Pat.singleton f) fields)) in
        let newObjTyp = TObject (mk_obj_typ 
                                   (List.map (fun (fieldName, fieldExp) -> 
                                     let fieldTyp = (Sub.inherits p env t (Pat.singleton fieldName)) in
                                     (* traceMsg "Check' EObject Checking field %s" fieldName; *)
                                     check env default_typ fieldExp fieldTyp;
                                     (Pat.singleton fieldName, Present, fieldTyp)) fields)
                                   absPat) in
        if not (Sub.subtype env newObjTyp typ) then
          Sub.typ_mismatch (Exp.pos exp)
            (Sub.TypTyp((fun t1 t2 -> sprintf "**expected %s, got %s" (string_of_typ t1) (string_of_typ t2)), 
                    typ, newObjTyp))
      | _ -> Sub.typ_mismatch p (Sub.Typ((fun t -> sprintf "expected TObject, got %s" (string_of_typ t)), typ))
    end
    | _ -> 
      traceMsg "About to synth:  %s\n" (string_of_exp exp);
      let synthed = Ext.extract_t (ExtTC.synth env default_typ exp) in
      traceMsg "Just synthed:  %s\n" (string_of_typ synthed);
      let synth_typ = simpl_typ env synthed in
      traceMsg "About to subtype:  %s <?: %s\n" (string_of_typ synth_typ)
        (string_of_typ typ);
      (* traceMsg "synthed is: %s | synth_typ is: %s"  *)
      (*   (string_of_typ synthed)  (string_of_typ synth_typ); *)
      (* traceMsg "About to subtype:  %s <?: %s" (string_of_typ synth_typ)  *)
      (*   (string_of_typ (expose_simpl_typ env typ)); *)
      if not (Sub.subtype env synth_typ typ) then begin
        Sub.typ_mismatch (Exp.pos exp)
          (Sub.TypTyp((fun t1 t2 -> sprintf "%%expected %s to have type %s, got %s" (string_of_exp exp) (string_of_typ (collapse_if_possible env t1)) (string_of_typ (collapse_if_possible env t2))), (expose_simpl_typ env typ), synth_typ))
      end (* else *)
  (* traceMsg "Checking finished." *)

  and synth (env : env) (default_typ : Typ.extTyp option) (exp : exp) : Typ.typ = 
    trace "Synth" (fun _ -> true) (synth' env default_typ) exp
  and synth' env (default_typ : Typ.extTyp option) exp : Typ.typ =
    let synth env defaultTyp exp =
      Ext.extract_t (ExtTC.synth env defaultTyp exp) in
    (* traceMsg "*Synthing type for %s" (string_of_exp exp); *)
    match exp with
    (* TODO: Pure if-splitting rule; make more practical by integrating with
       flow typing. *)
    | EIf (p, EInfixOp (_, "hasfield",  EDeref (_, EId (_, obj)), (EId (_, fld))),
           true_part, false_part) ->
      begin match expose_simpl_typ env (Ext.extract_t (Env.lookup_id obj env)), Ext.extract_t (Env.lookup_id fld env) with
      | TRef (_, TObject ot), TRegex pat -> 
        let subtract (p, pres, t) =
          if Pat.is_overlapped p pat then (Pat.subtract p pat, pres, t) (* perf *)
          else (p, pres, t) in
        let false_typ = synth env default_typ false_part in
        let true_typ =
          let fld_typ = Sub.simpl_lookup p env (TObject ot) pat in
          let env = Env.bind_typ_id "alpha" (Ext.embed_t (TRegex pat)) env in
          let env = Env.bind_id fld (Ext.embed_t (TId "alpha")) env in
          let env = Env.bind_id obj 
            (Ext.embed_t
               (TObject (mk_obj_typ ((Pat.var "alpha", Present, fld_typ) ::
                                     map subtract (fields ot))
                           (absent_pat ot)))) env in
          synth env default_typ true_part in
        Sub.typ_union env true_typ false_typ
      | s, t ->
        raise (Sub.Typ_error (p, Sub.TypTyp((fun t1 t2 -> sprintf "expected object and string types, got %s and %s"
          (string_of_typ t1) (string_of_typ t2)), s, t)))
      end
    | EConst (_, c) -> begin match c with
      | JavaScript_syntax.CString s -> TRegex (Pat.singleton s)
      | JavaScript_syntax.CRegexp _ -> TId "RegExp"
      | JavaScript_syntax.CNum _ -> TPrim "Num"
      | JavaScript_syntax.CInt _ -> TPrim "Num"
      | JavaScript_syntax.CBool true -> TPrim "True"
      | JavaScript_syntax.CBool false -> TPrim "False"
      | JavaScript_syntax.CNull -> TPrim "Null"
      | JavaScript_syntax.CUndefined -> TPrim "Undef"
    end
    | EBot _ -> TBot
    | EId (p, x) -> begin
      try 
        Ext.extract_t (Env.lookup_id x env)
      with Not_found -> match default_typ with
      | None -> raise (Sub.Typ_error (p, Sub.String(sprintf "%s is not defined", x))) (* severe *)
      | Some t -> let t = Ext.extract_t t in
        traceMsg "Warning: Unbound identifier %s at %s\n" x (Pos.toString p);
        traceMsg "Currently bound identifiers are:\n";
        IdMap.iter (fun id bs -> 
          if (List.exists (fun b -> match Ext.extract_b b with BTermTyp _ -> true | _ -> false) bs) 
          then traceMsg "%s, " id) env;
        t (* Should probably warn about undefined identifier here *)
    end
    | ELet (_, x, e1, e2) -> synth (Env.bind_id x (Ext.embed_t (synth env default_typ e1)) env) default_typ e2
    | ESeq (_, e1, e2) -> begin match synth env default_typ e1 with
      TBot -> (* e1 will not return; no need to typecheck e2 *)
        TBot
      | _ -> synth env default_typ e2
    end
    | EArray (p, []) -> 
      raise (Sub.Typ_error (p, Sub.FixedString "synth: an empty array literal requires a type annotation"))
    | EArray (p, e::es) -> 
      let (t1, ts) = synth env default_typ e, map (synth env default_typ) es in
      let tarr = List.fold_right (Sub.typ_union env) ts t1 in
      begin match simpl_typ env (mk_array_typ p env tarr) with
      | TRef (_, t) -> t
      | _ -> failwith "synth: mk_array_typ did not produce a TRef"
      end
    (* Optimization to avoid reducing TArray<'a> *)
    | ERef (p1, RefCell, EArray (p2, e::es)) ->
      let (t1, ts) = synth env default_typ e, map (synth env default_typ) es in
      let tarr = List.fold_right (Sub.typ_union env) ts t1 in
      mk_array_typ p2 env tarr
    | ERef (p, k, e) ->
      let t = synth env default_typ e in
      begin match k with
      | SourceCell -> TSource (None, t)
      | SinkCell -> TSink (None, t)
      | RefCell -> TRef (None, t)
      end
    | EDeref (p, e) -> 
      let typ = (synth env default_typ e) in
      (* traceMsg "In EDeref, synthed type of %s is %s" (string_of_exp e) (string_of_typ typ); *)
      let exposed_typ = expose_simpl_typ env typ in
      (* traceMsg "In EDeref, exposed type is %s" (string_of_typ typ); *)
      let typ = 
        try ((check_kind p env typ)) 
        with _ -> traceMsg "Bad kind for %s!" (string_of_typ typ); typ in
      if exposed_typ = TPrim "Unsafe"
      then raise (Sub.Typ_error (p, Sub.FixedString "synth: Cannot dereference an unsafe value"))
      else begin match typ with
      (* Auto-boxing of primitives *)
      | TPrim "Num" -> (match expose_simpl_typ env (TId "Number") with TRef (_, t) -> t | _ -> failwith "Impossible")
      | TRegex _ -> (match expose_simpl_typ env (TId "String") with TRef (_, t) -> t | _ -> failwith "Impossible")
      | _ -> match extract_ref ("EDeref: " ^ (string_of_exp e)) p env typ with
        | TRef (_, t) -> t
        | TSource (_, t) -> t
        | t -> raise (Sub.Typ_error (p, Sub.Typ((fun t -> sprintf "synth: cannot read an expression of type %s" (string_of_typ t)), t)))
      end 
    | ESetRef (p, e1, e2) ->
      let isConstructing = match e2 with (* Special case *)
        | EAssertTyp(_, t, e2) ->
          (match Ext.extract_t t with
          | TApp(TPrim "Constructing", [targ]) -> Some (targ, e2)
          | _ -> None)
        | _ -> None in
      begin match isConstructing with
      | Some (targ, e2) ->
        let makeOptional t =
          let (n, o) = match t with
            | TRef(n, TObject o) -> (n, o)
            | TSource(n, TObject o) -> (n, o)
            | TSink(n, TObject o) -> (n, o)
            | _ -> failwith "Impossible" in
          let f = fields o in
          let f' = List.map (fun (pat, presence, t) ->
            if (Pat.is_equal pat proto_pat ||
                  Pat.is_equal pat (Pat.singleton "-*- code -*-") ||
                  Pat.is_equal pat (Pat.singleton "prototype"))
            then (pat, presence, t)
            else (pat, Maybe, t)) f in
          let obj = (TObject (mk_obj_typ f' (absent_pat o))) in
          let ret = match t with
            | TRef _ -> TRef (n, obj)
            | TSource _ -> TSource (n, obj)
            | TSink _ -> TSink (n, obj)
            | _ -> failwith "Impossible" in
          ret in
        let tsimpl = simpl_typ env (expose_simpl_typ env targ) in
        begin match tsimpl with
        | TSource _
        | TRef _ ->
          let _ = check env default_typ e2 (makeOptional tsimpl) in
          synth env default_typ (ESetRef(p, e1, (ECheat (p, Ext.embed_t targ, e2))))  (* do the remaining checking for e1 *)
        | _ ->
          Sub.typ_mismatch p (Sub.Typ ((fun t ->
            sprintf "Expected Constructing<> to be applied to an object type; got %s"
              (string_of_typ targ)), targ));
          targ
        end
      | None ->
        let t = extract_ref "ESetRef" p env (expose_simpl_typ env (synth env default_typ e1)) in
        begin match t with
        | TRef (_, TUninit ty) -> begin match !ty with
          | None -> 
            let newTy = synth env default_typ e2 in
          (* traceMsg "Updating typ at %s to %s\n" (Pos.toString p) (string_of_typ newTy); *)
            ty := Some newTy;
            newTy
          | Some s -> (* traceMsg "Checking typ at %s\n" (Pos.toString p); *) check env default_typ e2 s; 
            s
        end
        | TRef (_, TPrim "Unsafe") -> TPrim "Unsafe" (* BSL: PUNTING ON ASSIGNMENT TO UNSAFE *)
        | TRef (_, s) 
        | TSink (_, s) -> 
        (* traceMsg "Synth ESetRef: Checking that %s has type %s" (string_of_exp e2) (string_of_typ s); *)
          check env default_typ e2 s; s
        | s -> 
          Sub.typ_mismatch p (Sub.Typ((fun t -> sprintf "left-hand side of assignment has type %s" (string_of_typ t)), s));
          s
        end
      end
    | ELabel (p, lbl, e) -> 
      (* This is a valid assumption for JavaScript. *)
      (* traceMsg "Synth: Binding label %s in expression %s" lbl (string_of_exp e); *)
      check (Env.bind_lbl lbl (Ext.embed_t (TPrim "Undef")) env) default_typ e (TPrim "Undef");
      TPrim "Undef"
    | EBreak (p, lbl, e) ->
      let lbl_typ = 
        try Ext.extract_t (Env.lookup_lbl lbl env)
        with Not_found -> (* severe *)
          raise (Sub.Typ_error (p, Sub.String (sprintf "synth: label %s is not defined", lbl))) in
      check env default_typ e lbl_typ;
      TBot
    | ETryCatch (p, e1, x, e2) ->
      let t1 = synth env default_typ e1
      and t2 = synth (Env.bind_id x (Ext.embed_t TTop) env) default_typ e2 in
      Sub.typ_union env t1 t2
    | ETryFinally (_, e1, e2) -> 
      let _ = synth env default_typ e1 in
      synth env default_typ e2
    | EThrow (_, e) -> 
      let _ = synth env default_typ e in
      TBot
    | ETypecast (p, rt, e) -> 
      let t = synth env default_typ e in
      Ext.extract_t (Static.static env rt (Ext.embed_t t))
    | EIf (p, e1, e2, e3) ->
      (match synth env default_typ e1 with
      | TPrim "True" -> synth env default_typ e2
      | TPrim "False" -> synth env default_typ e3
      | t (* when subtype env t typ_bool *) ->
        Sub.typ_union env (synth env default_typ e2) (synth env default_typ e3)
    (* | _ -> raise (Sub.Typ_error (p, Sub.FixedString "synth: Got non-bool type for condition of if expression")) *) )
    | EObject (p, fields) ->
      let mk_field (name, exp) = 
        (Pat.singleton name, Present, synth env default_typ exp) in
      let get_names (name, _) names = 
        Pat.union names (Pat.singleton name) in
      let rest = List.fold_right get_names fields (Pat.singleton "__proto__") in
      if List.mem "__proto__" (map fst fields) then
        TObject (mk_obj_typ (map mk_field fields) (Pat.negate rest))
      else
        TObject (mk_obj_typ ((Pat.singleton "__proto__", Present, TId "Object") 
                             :: (map mk_field fields))
                   (Pat.negate rest))
    | EBracket (p, obj, field) -> 
      begin match expose_simpl_typ env (synth env default_typ field) with
      | TRegex pat -> begin
        match synth env default_typ obj with
        | TRegex _ -> Sub.inherits p env (TId "String") pat
        | obj_typ -> 
          Sub.inherits p env (un_null obj_typ) pat
      end
      | idx_typ -> 
        raise (Sub.Typ_error
                 (p, Sub.Typ((fun t -> sprintf "index has type %s" (string_of_typ t)), idx_typ)))
      end
    | EUpdate (p, obj, field, value) -> begin
      let tobj = synth env default_typ obj in
      (* traceMsg "EUpdate1: Synthed type for object %s is\n%s" (string_of_exp obj) (string_of_typ tobj); *)
      (* traceMsg "EUpdate2: Synthed type for value %s is\n%s" (string_of_exp value) (string_of_typ (synth env default_typ value)); *)
      (* traceMsg "EUpdate3: %s" (string_of_bool (subtype env (synth env default_typ value) (expose env (TId "Ext")))); *)
      match expose_simpl_typ env tobj, 
      expose_simpl_typ env (synth env default_typ field)(* , synth env default_typ value *) with
      | TObject o, TRegex idx_pat (* (TRegex idx_pat as tfld), typ *) ->
        begin
          if not (Pat.is_subset (Sub.pat_env env) 
                    idx_pat (cover_pat o))
          then
            Sub.typ_mismatch p (Sub.Pat((fun p -> sprintf "synth: %s affects hidden fields" (Pat.pretty p)), idx_pat))
        end;
        begin
          if Pat.is_overlapped idx_pat (absent_pat o) then
            (* traceMsg "ERROR: %s failed at field '%s' \nwith type %s, \nwhen absent_pat = %s in typ %s\n" (string_of_exp exp) (Pat.pretty idx_pat) (string_of_typ typ) (Pat.pretty (absent_pat o)) (string_of_typ tobj); *)
            Sub.typ_mismatch p (Sub.PatPatTyp((fun p1 p2 t -> sprintf "synth: Assigning to field '%s' when absent_pat = %s in typ %s" (Pat.pretty p1) (Pat.pretty p2) (string_of_typ t)), idx_pat, (absent_pat o), tobj))
        end;
        let fs : field list = fields o in
        let okfield (fld_pat, pres, s) = 
          if Pat.is_overlapped fld_pat idx_pat (* && not (subtype env (expose env typ) (expose env s)) *) then
            (* try *)
            (*   Sub.with_typ_exns check  *)
            (* Sub.typ_mismatch p *)
            (*   (Sub.TypTypTyp((fun t1 t2 t3 ->  *)
            (*     sprintf "synth, field update: %s, the new value, is not subtype of %s at index %s" *)
            (*       (string_of_typ t1) (string_of_typ t2) (string_of_typ t3)), typ, s, tfld)) in *)
            check env default_typ value s in
        let _ = List.iter okfield fs in
        tobj
      | obj, fld ->
        let _ = Sub.typ_mismatch p (Sub.TypTyp((fun t1 t2 -> 
          sprintf "Bad update: expected TObject, TRegex, and got %s and %s"
            (string_of_typ t1) (string_of_typ t2)), obj, fld)) in
        obj
          
    end
    | EPrefixOp (p, op, e) -> synth env default_typ (EApp (p, EId (p, op), [e]))
    | EInfixOp (p, op, e1, e2) -> synth env default_typ (EApp (p, EId (p, op), [e1; e2]))
    | EApp (p, f, args) -> 
      traceMsg "Strobe_synth: EApp with function %s | args %s" (string_of_exp f)
         (List.fold_left (fun acc a -> (acc ^ (string_of_exp a))) "" args);
      check_app env default_typ f args (un_null (synth env default_typ f))
    | ERec (p, binds, body) -> 
      (* No kinding check here, but it simply copies the type from the function.
         Let it work. (Actual reason: no position available) *)
      let f env (x, t, e) = Env.bind_id x t env in
      let env = fold_left f env binds in
      let tc_bind (x, t, e) = check env default_typ e (Ext.extract_t t) in
      List.iter tc_bind binds;
      synth env default_typ body 
    | EFunc (p, args, func_info, body) -> 
      (* BSL: Synthesizing Ext *)
      let thisType = if usesThis body then TThis (TId "Ext") else TThis (TPrim "Unsafe") in
      let arrowTyp = TArrow([thisType], Some (TId "Ext"), TId "Ext") in
      (* traceMsg "Checking expression for Ext-arrow: %s" (string_of_exp exp); *)
      check env default_typ exp arrowTyp;
      arrowTyp
    | ESubsumption (p, t, e) ->
      let t = check_kind p env (Ext.extract_t t) in
      check env default_typ e t;
      t
    | EAssertTyp (p, t, e) ->
      (* traceMsg "Synth: AssertTyp that %s has type %s" (string_of_exp e) (string_of_typ t); *)
      (* traceMsg "%s" (string_of_bool (subtype env (synth env default_typ e) t)); *)
      let t = check_kind p env (Ext.extract_t t) in
      let _ = check env default_typ e t in
      t
    | EDowncast (p, t, e) -> 
      let t = check_kind p env (Ext.extract_t t) in
      ignore (synth env default_typ e);
      t
    | ETypAbs (p, x, t, e) ->
      (* bind_typ_id does the kinding check *)
      let env = Env.bind_typ_id x t env in
      TForall (None, x, Ext.extract_t t, synth env default_typ e)
    | ETypApp (p, e, u) ->
      let u = Ext.extract_t u in
      begin match expose_simpl_typ env (synth env default_typ e) with
      | TForall (n, x, s, t) ->
        if Sub.subtype env u s then
          apply_name n (canonical_type (typ_subst x u t))
        else 
          begin
            Sub.typ_mismatch p
              (Sub.TypTyp((fun t1 t2 -> sprintf "type-argument %s is not a subtype of the bound %s"
                (string_of_typ t1) (string_of_typ t2)), u, s));
            canonical_type (typ_subst x s t) (* Warning: produces possibily spurious errors *)
          end
      | TEmbed t ->
        Ext.extract_t (ExtTC.synth env default_typ exp)
      | t ->
        (* traceMsg "In ETypApp, and things went badly wrong with %s" (string_of_typ t); *)
        raise
          (Sub.Typ_error (p, Sub.TypTyp((fun t1 t2 -> 
            sprintf "expected forall-type in type application, got:\n%s\ntype argument is:\n%s"
              (string_of_typ t1) (string_of_typ t2)), t, u)))
      end
    | ECheat (p, t, _) -> 
      let t = Ext.extract_t t in
      (* traceMsg "Cheating to %s" (string_of_typ (replace_name None t)); *)
      let simpl_t = check_kind p env t in
      (* let simpl_t = Typ.trace "Exposing type" "" (fun _ -> true) (fun () -> expose_simpl_typ env (check_kind p env t)) in *)
      (* traceMsg "Exposed typ is %s" (string_of_typ (replace_name None simpl_t)); *)
      simpl_t
    | EParen (p, e) ->  synth env default_typ e

  and synths env default_typ es = map (synth env default_typ) es

  and check_app env default_typ f args tfun =
    let p = pos f in
    let check_app = check_app env default_typ f args in
    traceMsg "Checking EApp@%s with function type %s" (Pos.toString p) (string_of_typ tfun);
    match expose_simpl_typ env tfun with 
      | TArrow (expected_typs, None, result_typ) -> 
        let args = fill (List.length expected_typs - List.length args) 
          (EConst (p, JavaScript_syntax.CUndefined)) args in
        begin
          try List.iter2 (check env default_typ) args expected_typs
          with Invalid_argument "List.iter2" -> 
            Sub.typ_mismatch p
              (Sub.NumNum(sprintf "arity-mismatch:  %d args expected, but %d given",
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
      | TInter (n, t1, t2) -> 
        (* Trying for **ORDERED** Intersection *)
        (Sub.with_typ_exns
           (fun () ->
             try let res = check_app t1 in
             res
             with Sub.Typ_error _ -> check_app t2))
      (* Sub.with_typ_exns *)
      (*   (fun () -> *)
      (*     try  *)
      (*       let r1 = check_app t1 in  *)
      (*       begin  *)
      (*         try *)
      (*           let r2 = check_app t2 in *)
      (*           apply_name n (typ_intersect env r1 r2) *)
      (*         with | Sub.Typ_error _ -> r1 *)
      (*       end *)
      (*     with | Sub.Typ_error _ -> check_app t2) *)
      | TUnion (n, t1, t2) ->
        let typ_or_err t = Sub.with_typ_exns (fun () -> try Some (check_app t) with Sub.Typ_error _ -> None) in
        let r1 = typ_or_err t1 in
        let r2 = typ_or_err t2 in
        (match r1, r2 with
        | Some r, None
        | None, Some r -> apply_name n r
        | _ -> raise (Sub.Typ_error (p, Sub.FixedString "synth2: Ambiguous union of functions")))
      | ((TForall _) as quant_typ)
      | ((TEmbed _) as quant_typ) -> 
        begin match forall_arrow quant_typ with
        | None -> 
          raise (Sub.Typ_error (p, Sub.Typ((fun t -> sprintf "synth: expected function, got %s"
            (string_of_typ t)), quant_typ)))
        | Some ([], (TArrow _ as arr)) -> check_app arr
        | Some (typ_vars, (TArrow (expected_typs, variadic, r) as arrow_typ)) -> 
          let print_binding (x,b) = match Ext.extract_b b with
            | BTypBound (b, _) -> traceMsg "Typ-bound %s %s" x (string_of_typ b)
            | _ -> traceMsg "Weird bound"
          in
          List.iter print_binding typ_vars;
          (* NEW ALGORITHM:
           * incrementally try checking arguments against a partial association, and if it works,
           * move on; otherwise, synth a type and build a new association, and try again
          *)
          let args = fill (List.length expected_typs - List.length args) 
            (EConst (p, JavaScript_syntax.CUndefined)) args in
          let expected_typs = if (List.length expected_typs < List.length args) then
              match variadic with
              | None -> 
                raise 
                  (Sub.Typ_error 
                     (p, Sub.FixedString(sprintf "synth: [Any] Ref ({|[Any]  Ref (a) -> /.*/|})-> /.*/expected %d arguments in a fixed-arity function, got %d"
                                           (List.length expected_typs) (List.length args))))
              | Some t -> 
                fill (List.length args - List.length expected_typs) t expected_typs 
            else expected_typs in
          
          let substitution_for (wanted : Typ.typ list) (offered : Typ.typ list) p typs t =
            Ext.extract_t 
              (ExtTC.assoc_sub env
                 (Ext.embed_t (TArrow (List.rev wanted, None, TTop)))
                 (Ext.embed_t (TArrow (List.rev offered, None, TTop)))
                 p typs (Ext.embed_t t)) in
          let check_tc exp (typ : Typ.typ) =
            (* let from_typ_vars = IdSetExt.from_list (map fst typ_vars) in *)
            (* let free_ids = free_typ_ids typ in *)
            (* let any_free = IdSet.inter from_typ_vars free_ids in *)
            (* if not (IdSet.is_empty any_free) then *)
            (*   false *)
            (* else  *)
              try
                   Sub.with_typ_exns (fun () -> 
                     check env default_typ exp typ); true
              with _ -> false in                
          let try_argument (found_subst, rev_expecteds, rev_syntheds, sub) (expected_typ : Typ.typ) arg =
            traceMsg "In EApp, expected = %s, arg = %s" (string_of_typ expected_typ) (string_of_exp arg);
            let check_succeeded =
              try Sub.with_typ_exns
                    (fun () -> let subst_typ = sub p typ_vars expected_typ in
                               traceMsg "Substituted type = %s\n" (string_of_typ subst_typ);
                               traceMsg "Checking %s : %s\n" (string_of_exp arg) (string_of_typ subst_typ);
                               let result = check_tc arg subst_typ in
                               traceMsg "Succeeded? %b\n" result;
                               result)
              with _ -> false in
            traceMsg "Check succeeded = %b" check_succeeded;
            if check_succeeded
            then begin
              (true, expected_typ :: rev_expecteds, expected_typ :: rev_syntheds, sub)
            end else 
              let synthed = synth env default_typ arg in
              traceMsg "Synthed argument type = %s" (string_of_typ synthed);
              let rev_expected' = expected_typ :: rev_expecteds in
              let rev_synthed' = (expose_simpl_typ env synthed) :: rev_syntheds in
              let sub' = substitution_for rev_expected' rev_synthed' in
              (* traceMsg "Computed new substitution"; *)
              (found_subst, rev_expected', rev_synthed', sub') in
          (* traceMsg "Got %d expected_typs, %d offered arguments" (List.length expected_typs) (List.length args); *)
          let (found_subst, _, _, sub) = List.fold_left2 try_argument (false, [], [], (fun _ _ t -> t)) expected_typs args in
            

          (* (\* guess-work breaks bidirectionality *\) *)
          let arg_typs = map (synth env default_typ) args in
          traceMsg "In EApp, arg_typs are:"; 
          List.iter (fun t -> traceMsg "  %s" (string_of_typ t)) arg_typs;
           traceMsg "1In Eapp, arrow_typ is %s" (string_of_typ arrow_typ); 
           traceMsg "2In Eapp, tarrow is    %s" 
             (string_of_typ (TArrow (arg_typs, None, r)));
          (* let sub = (ExtTC.assoc_sub env  *)
    (*         (\* NOTE: Can leave the return type out, because we're just *)
    (*                  copying it, so it will never yield any information *\) *)
    (*         (Ext.embed_t (TArrow (expected_typs, None, TTop))) *)
          (*   (\* Need to expose arg_typs before association to eliminate TIds *\) *)
          (*   (Ext.embed_t (TArrow ((List.map (fun t ->  *)
          (*     expose_simpl_typ env t) arg_typs),  *)
          (*                         None, TTop)))) in *)
           traceMsg "3In Eapp, original return type is %s" (string_of_typ r); 
            let ret = (sub p typ_vars r) in
             traceMsg "4In Eapp, substituted return type is %s" (string_of_typ ret); 
            ret

          (* IdMap.iter (fun k t -> *)
          (*   traceMsg "  [%s => %s]" k (string_of_typ t)) assoc; *)
          (* let guess_typ_app exp typ_var =  *)
          (*   try *)
          (*     let guessed_typ =  *)
          (*       try IdMap.find typ_var assoc *)
          (*       with Not_found -> *)
          (*         if (List.length expected_typs > List.length args)  *)
          (*         then (TPrim "Undef") *)
          (*         else raise Not_found in *)
          (*     ETypApp (p, exp, Ext.embed_t guessed_typ) *)
          (*   with Not_found -> begin *)
          (*     raise (Sub.Typ_error  *)
          (*              (p, Sub.FixedString (sprintf "synth: could not instantiate typ_var %s" typ_var))) end in *)
          (* let guessed_exp =  *)
          (*   fold_left guess_typ_app (ECheat (p, Ext.embed_t quant_typ, f))  *)
          (*     typ_vars in *)
          (* let synthed_exp = EApp(p, guessed_exp, assumed_arg_exps) in *)
          (* traceMsg "In EApp, synthed_exp = %s" (Exp.string_of_exp synthed_exp); *)
          (* synth env default_typ synthed_exp *)
        | Some (_, TEmbed t) -> Ext.extract_t (ExtTC.check_app env default_typ f args t)
        | Some _ -> failwith "expected TArrow from forall_arrow"
        end
      | not_func_typ -> 
        (* even in an intersection, this should count as a genuine error *)
        raise (Sub.Typ_error 
                 (p, Sub.Typ((fun t -> sprintf "expected function, got %s" (string_of_typ t)), not_func_typ)))

  let typecheck env default_typ exp =
    let _ = synth env default_typ exp in
    ()
end
