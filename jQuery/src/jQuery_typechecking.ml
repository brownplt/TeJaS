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
  with type binding = JQ.binding
  with type baseTyp = JQ.baseTyp
  with type baseKind = JQ.baseKind
  with type baseBinding = JQ.baseBinding
  with type env = JQ.env)
  (Kind : JQuery_sigs.JQUERY_KINDING
   with type typ = JQ.typ
  with type kind = JQ.kind
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


  let trace msg success thunk exp = (* thunk exp *) StrobeTC.trace msg success thunk exp
    
  let bind_sigma x s e = match s with
    | STyp t -> Env.bind_typ_id x t e
    | SMult m -> Env.bind_mult_id x m e

  let rec bind_forall_vars (env : env) (typ : typ) : env * typ = match typ with
    | TForall (n, x, s, t) -> bind_forall_vars (bind_sigma x s env) (apply_name n t)
    | TStrobe t -> let (env, t) = StrobeTC.bind_forall_vars env t in (env, embed_t t)
    | typ -> (env, typ)

  let disable_flows () = StrobeTC.disable_flows () 
  (* need () because otherwise this is a value, not a function, and ML gets angry at that *)

  let rec forall_arrow (typ : typ) : (id list * typ) option = match typ with
    | TStrobe s -> begin
      match StrobeTC.forall_arrow s with
      | None -> None
      | Some (ids, t) -> Some (ids, embed_t t)
    end
    | TForall (_, x, _, typ') -> begin match forall_arrow typ' with
      | None -> None
      | Some (xs, t) -> Some (x :: xs, t)
    end
    | _ -> None

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
    trace "Synth" (fun _ -> true) (synth' env default_typ) exp
  and synth' env default_typ exp : typ = match exp with
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

  let typecheck env default_typ exp =
    let _ = synth env default_typ exp in
    ()

end
