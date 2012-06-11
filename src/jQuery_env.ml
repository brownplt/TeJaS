open Prelude
open JQuery_syntax
open FormatExt
open TypImpl

module List = ListExt
exception Not_wf_typ of string

type env = {
  id_typs : typ IdMap.t; (* type of term identifiers *)
  typ_ids: sigma IdMap.t; (* bounded type variables *)
}

let print_env env fmt : unit =
  let unname t = if (!TypImpl.Pretty.useNames) then replace_name None t else t in
  vert [text "Types of term identifiers:";
        vert (List.map (fun (id, t) -> 
          horz [text id; text "="; (TypImpl.Pretty.typ (unname t))]) (IdMapExt.to_list env.id_typs));
        empty; 
        text "Bounded type variables:";
        vert (List.map (fun (id, s) -> 
          horz [text id; 
                vert [horz [text "="; 
                            match s with
                            | STyp t -> TypImpl.Pretty.typ (unname t)
                            | SMult m -> TypImpl.Pretty.multiplicity m]]]) (IdMapExt.to_list env.typ_ids));
        empty
       ] 
    fmt;
  Format.pp_print_flush fmt ()


let empty_env = { 
  id_typs = IdMap.empty;
  typ_ids = IdMap.empty;
}

let bind_id x t env  = { env with id_typs = IdMap.add x t env.id_typs }

let bind_typ_id x s env = { env with typ_ids = IdMap.add x s env.typ_ids }
  

let lookup_id x env = IdMap.find x env.id_typs

let lookup_typ_id x env = IdMap.find x env.typ_ids


let id_env env = env.id_typs


let dom env = IdSetExt.from_list (IdMapExt.keys env.id_typs)

let rec bind_typ env typ : env * typ = match typ with
  | TForall (n, x, s, t) -> bind_typ (bind_typ_id x s env) (apply_name n t)
  | typ -> (env, typ)
