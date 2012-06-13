open Prelude
open JQuery_syntax
open FormatExt
open TypImpl

module List = ListExt
exception Not_wf_typ of string

let partition_env (env : env) =
  IdMap.fold (fun id bind (ids, typs, mults) -> match bind with
  | BTermTyp t -> (IdMap.add id t ids, typs, mults)
  | BTypBound (t, k) -> (ids, IdMap.add id (t, k) typs, mults)
  | BMultBound (m, k) -> (ids, typs, IdMap.add id (m, k) mults)) env (IdMap.empty, IdMap.empty, IdMap.empty)

let print_env env =
  let (id_typs, typ_ids, mult_ids) = partition_env env in
  let unname t = if (!TypImpl.Pretty.useNames) then replace_name None t else t in
  let cut : printer = fun fmt -> Format.pp_print_cut fmt () in
  [cut;
   squish [IdMapExt.p_map "Types of term identifiers: " empty
              text (fun t -> TypImpl.Pretty.typ (unname t)) 
              id_typs;
           text ","];
   squish [IdMapExt.p_map "Bounded type variables: " empty
              text 
              (fun (t, k) -> 
                vert [horz [text "="; TypImpl.Pretty.typ (unname t)];
                      horz [text "::"; TypImpl.Pretty.kind k]]) typ_ids;
           text ","];
   IdMapExt.p_map "" empty
     text
     (fun (m, k) -> 
       vert [horz [text "="; TypImpl.Pretty.multiplicity m];
             horz [text "::"; TypImpl.Pretty.kind k]]) mult_ids;
   cut
  ]


let empty_env : env = IdMap.empty

let kind_check env recIds (s : sigma) : kind  =
  JQuery_kinding.kind_check_sigma env recIds s

let bind_id x t env = IdMap.add x (BTermTyp t) env

let bind_rec_typ_id (x : id) recIds (s : sigma) (env : env) = 
  let k = kind_check env recIds s in
  match s with
  | STyp t -> IdMap.add x (BTypBound(t, k)) env
  | SMult m -> IdMap.add x (BMultBound(m, k)) env

let bind_typ_id x t env = bind_rec_typ_id x [] t env

let bind_recursive_types (xts : (id * typ) list) (env : env) =
  let env' = List.fold_left (fun ids (x, t) -> IdMap.add x (BTypBound(t, KStar)) ids) env xts in
  timefn "Bindrec/Kind checking" (List.fold_left (fun env (x, t) -> bind_typ_id x (STyp t) env) env') xts

let unchecked_bind_typ_ids (xts : (id * typ) list) (env : env) =
  List.fold_left (fun ids (x, t) -> IdMap.add x (BTypBound(t, KStar)) ids) env  

let lookup_id x env = 
  match IdMap.find x env with BTermTyp t -> t | _ -> raise Not_found

let lookup_typ_id x env = 
  match IdMap.find x env with BTypBound (t,k) -> (t,k) | _ -> raise Not_found

let rec bind_typ env typ : env * typ = match typ with
  | TForall (n, x, s, t) -> bind_typ (bind_typ_id x s env) (apply_name n t)
  | typ -> (env, typ)
