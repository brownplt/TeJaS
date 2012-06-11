open Prelude
open JQuery_syntax
open FormatExt
open TypImpl

module List = ListExt
exception Not_wf_typ of string

type env = {
  id_typs : typ IdMap.t; (* type of term identifiers *)
  typ_ids: (typ * kind) IdMap.t; (* bounded type variables *)
  mult_ids: (multiplicity * kind) IdMap.t; (* bounded multiplicity variables *)
}

let print_env env fmt : unit =
  let unname t = if (!TypImpl.Pretty.useNames) then replace_name None t else t in
  vert [text "Types of term identifiers:";
        vert (List.map (fun (id, t) -> 
          horz [text id; text "="; (TypImpl.Pretty.typ (unname t))]) (IdMapExt.to_list env.id_typs));
        empty; 
        text "Bounded type variables:";
        vert (List.map (fun (id, (t, k)) -> 
          horz [text id; 
                vert [horz [text "="; TypImpl.Pretty.typ (unname t)];
                      horz [text "::"; TypImpl.Pretty.kind k]]]) (IdMapExt.to_list env.typ_ids));
        vert (List.map (fun (id, (m, k)) -> 
          horz [text id; 
                vert [horz [text "="; TypImpl.Pretty.multiplicity m];
                      horz [text "::"; TypImpl.Pretty.kind k]]]) (IdMapExt.to_list env.mult_ids));
        empty
       ] 
    fmt;
  Format.pp_print_flush fmt ()


let empty_env = { 
  id_typs = IdMap.empty;
  typ_ids = IdMap.empty;
  mult_ids = IdMap.empty;
}


let kind_check env recIds (s : sigma) : kind  =
  JQuery_kinding.kind_check_sigma ((IdMap.map (fun (_, k) -> k) env.typ_ids),
                                   (IdMap.map (fun (_, k) -> k) env.mult_ids)) recIds s

let bind_id x t env  = { env with id_typs = IdMap.add x t env.id_typs }

let bind_rec_typ_id (x : id) recIds (s : sigma) (env : env) = 
  let k = kind_check env recIds s in
  match s with
  | STyp t -> { env with typ_ids = IdMap.add x (t, k) env.typ_ids }
  | SMult m -> { env with mult_ids = IdMap.add x (m, k) env.mult_ids }

let bind_typ_id x t env = bind_rec_typ_id x [] t env

let bind_recursive_types (xts : (id * typ) list) (env : env) =
  let typ_ids' = List.fold_left (fun ids (x, t) -> IdMap.add x (t, KStar) ids) env.typ_ids xts in
  let env' = {env with typ_ids = typ_ids'} in
  timefn "Bindrec/Kind checking" (List.fold_left (fun env (x, t) -> bind_typ_id x (STyp t) env) env') xts

let unchecked_bind_typ_ids (xts : (id * typ) list) (env : env) =
  let typ_ids' = List.fold_left (fun ids (x, t) -> IdMap.add x (t, KStar) ids) env.typ_ids xts in
  {env with typ_ids = typ_ids'}
  

let lookup_id x env = IdMap.find x env.id_typs

let lookup_typ_id x env = IdMap.find x env.typ_ids


let id_env env = env.id_typs


let dom env = IdSetExt.from_list (IdMapExt.keys env.id_typs)

let rec bind_typ env typ : env * typ = match typ with
  | TForall (n, x, s, t) -> bind_typ (bind_typ_id x s env) (apply_name n t)
  | typ -> (env, typ)
