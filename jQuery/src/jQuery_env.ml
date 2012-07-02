open Prelude
open Sig
open Strobe_sigs
open JQuery_sigs

module List = ListExt
exception Not_wf_typ of string

module MakeExt
  (JQuery : JQUERY_MODULE)
  (JQueryKinding : JQUERY_KINDING
   with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type multiplicity = JQuery.multiplicity
  with type sigma = JQuery.sigma
  with type binding = JQuery.binding
  with type baseTyp = JQuery.baseTyp
  with type baseKind = JQuery.baseKind
  with type baseBinding = JQuery.baseBinding
  with type env = JQuery.env) 
  (Env : TYP_ENV
   with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type binding = JQuery.binding
  with type env = JQuery.env)
  : (TYP_ENV
     with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type binding = JQuery.binding
  with type env = JQuery.env
  with type env_decl = Env.env_decl) =
struct
  type typ = Env.typ
  type kind = Env.kind
  type binding = Env.binding
  type env = Env.env
  type env_decl = Env.env_decl
  open Env
  open JQueryKinding

  let print_env = Env.print_env
  let parse_env_buf = Env.parse_env_buf
  let parse_env = Env.parse_env
  let parse_env_file = Env.parse_env_file

  let bind x b env = IdMap.add x b env

  let kind_check env recIds (s : sigma) : kind  =
    JQueryKinding.kind_check_sigma env recIds s

  let bind_rec_typ_id (x : id) recIds (s : sigma) (env : env) = 
    let k = kind_check env recIds s in
    match s with
    | STyp t -> IdMap.add x (BStrobe (JQuery.Strobe.BTypBound(JQuery.extract_t t, 
                                                              JQuery.extract_k k))) env
    | SMult m -> IdMap.add x (BMultBound(m, k)) env

  let bind_typ_id x s env = bind_rec_typ_id x [] s env

  let bind_recursive_types (xts : (id * typ) list) (env : env) =
    let env' = List.fold_left (fun ids (x, t) -> 
      IdMap.add x (BStrobe (JQuery.Strobe.BTypBound(JQuery.extract_t t, 
                                                    JQuery.Strobe.KStar))) ids) env xts in
    timefn "Bindrec/Kind checking" (List.fold_left (fun env (x, t) -> bind_typ_id x (STyp t) env) env') xts

  let unchecked_bind_typ_ids (xts : (id * typ) list) (env : env) =
    List.fold_left (fun ids (x, t) -> 
      IdMap.add x (BStrobe (JQuery.Strobe.BTypBound(JQuery.extract_t t, JQuery.Strobe.KStar))) ids) env xts

  let lookup_id x env = 
    match JQuery.extract_b (IdMap.find x env) with
    | JQuery.Strobe.BTermTyp t -> t
    | _ -> raise Not_found

  let lookup_typ_id x env = 
    match JQuery.extract_b (IdMap.find x env) with
    | JQuery.Strobe.BTypBound (t,k) -> (t,k)
    | _ -> raise Not_found

  (* let rec bind_typ env typ : env * typ = match typ with *)
  (*   | TForall (n, x, s, t) -> bind_typ (bind_typ_id x s env) (apply_name n t) *)
  (*   | typ -> (env, typ) *)
end
