open Prelude
open JQuery_syntax
open TypImpl

exception Kind_error of string

type kind_env = kind IdMap.t * kind IdMap.t

let valid_prims = ref (IdSetExt.from_list [ ])

let list_prims () = IdSetExt.to_list !valid_prims

let new_prim_typ (s : string) : unit =
  if IdSet.mem s !valid_prims then
    raise (Kind_error (s ^ " is already defined as a primitive type"))
  else (
    (* Printf.printf "Adding prim %s\n" s; *)
    valid_prims := IdSet.add s !valid_prims)

let kind_mismatch s calculated_kind expected_kind = 
  raise 
    (Kind_error 
       (sprintf "Expected kind %s, but got kind %s for type:\n%s"
          (string_of_kind expected_kind)
          (string_of_kind calculated_kind)
          (match s with STyp typ -> string_of_typ typ | SMult m -> string_of_mult m)))
let kind_mismatch_typ t calc exp = kind_mismatch (STyp t) calc exp

let rec well_formed_kind k = match k with
  | KStar -> true
  | KMult (KArrow _) -> false
  | KMult k -> well_formed_kind k
  | KArrow (args, ret) -> 
    List.for_all (fun k -> match k with 
    | KArrow _ -> false
    | _ -> well_formed_kind k) args
      && well_formed_kind ret

let rec kind_check_sigma (env : kind_env) (recIds : id list) (s : sigma) : kind = match s with
  | STyp t -> kind_check_typ env recIds t
  | SMult m -> kind_check_mult env recIds m

and kind_check_typ (env : kind_env) (recIds : id list) (typ : typ) : kind = match typ with
  | TTop
  | TBot
  | TRegex _ -> KStar
  | TPrim s -> 
    if IdSet.mem s !valid_prims then 
      KStar
    else
      raise (Kind_error (s ^ " is not a primitive type"))
  | TUnion (_, t1, t2)
  | TInter (_, t1, t2) ->
    let k1 = kind_check_typ env recIds t1 in
    let k2 = kind_check_typ env recIds t2 in
    if k1 <> k2 then kind_mismatch_typ t1 k1 k2 else k1
  | TArrow (_, arg_typs, varargs, result_typ) ->
    let assert_kind t = match kind_check_typ env recIds t with
      | KMult _
      | KStar -> ()
      | k -> kind_mismatch_typ t k KStar in
    List.iter assert_kind (result_typ :: arg_typs);
    (match varargs with None -> () | Some v -> assert_kind v);
    KStar
  | TId x -> 
    begin 
      try IdMap.find x (fst env)
      with Not_found ->
        if (not (List.mem x recIds)) then
          (* let strfmt = Format.str_formatter in *)
          (* let envText = (IdMap.iter (fun id k ->  *)
          (*   FormatExt.horz [FormatExt.text id; FormatExt.text "="; Pretty.kind k] strfmt; *)
          (*   Format.pp_print_newline strfmt () *)
          (* ) env); Format.flush_str_formatter() in *)
          let s = (sprintf "type variable %s is unbound in env" x (* envText *)) in
          (* Printf.printf "%s" s; print_newline(); *)
          raise (Kind_error s)
        else KStar
    end
  | TForall (_, x, s, t) ->
    let k1 = kind_check_sigma env recIds s in
    let k2 = kind_check_typ ((IdMap.add x KStar (fst env)), snd env) recIds t in
    if k1 <> k2 then kind_mismatch_typ t k1 k2 else k1
  | TLambda (_, args, t) ->
    let env' = fold_right (fun (x, k) env -> 
      match k with
      | KMult _ -> (fst env, IdMap.add x k (snd env))
      | _ -> (IdMap.add x k (fst env), snd env)) args env in
    KArrow (List.map snd2 args, kind_check_typ env' recIds t)
  | TApp (t_op, s_args) ->
    begin 
      let check k_arg s_arg = 
        let k_actual = kind_check_sigma env recIds s_arg in
        if k_arg = k_actual then
          ()
        else 
          kind_mismatch s_arg k_actual k_arg in
      match t_op with
      (* | TPrim ("Constructing" as p) *)
      (* | TPrim ("Mutable" as p)  *)
      (* | TPrim ("Immutable" as p) -> *)
      (*   begin  *)
      (*     try List.iter2 check [KStar] s_args *)
      (*     with Invalid_argument _ -> raise (Kind_error (p ^ "<> expects one argument")) *)
      (*   end; *)
      (*   KStar *)
      | _ -> match kind_check_typ env recIds t_op with
        | KArrow (k_args, k_result) ->
          begin 
            try
              List.iter2 check k_args s_args;
              k_result
            with Invalid_argument _ ->
              raise (Kind_error
                       (sprintf "operator expects %d args, given %d"
                          (List.length k_args) (List.length s_args)))
          end
        | KMult _
        | KStar ->
          raise (Kind_error 
                   (sprintf "not a type operator:\n%s" (string_of_typ t_op)))
    end

and kind_check_mult _ _ _ = KStar
