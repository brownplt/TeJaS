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
  and synth' env default_typ exp : typ =
    embed_t (StrobeTC.synth env default_typ exp)

  let typecheck env default_typ exp =
    let _ = synth env default_typ exp in
    ()

end
