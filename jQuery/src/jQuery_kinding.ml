open Prelude
open Sig
open JQuery_sigs
open Strobe_sigs


module Make
  (JQuery : JQUERY_MODULE)
  (StrobeKind : STROBE_KINDING
             with type typ = JQuery.baseTyp
  with type kind = JQuery.baseKind
  with type binding = JQuery.baseBinding
  with type extTyp = JQuery.typ
  with type extKind = JQuery.kind
  with type extBinding = JQuery.binding
  with type env = JQuery.env) =
struct
  include JQuery
  open JQuery
      
  let list_prims = StrobeKind.list_prims
  let new_prim_typ = StrobeKind.new_prim_typ

  let kind_mismatch s calculated_kind expected_kind = 
    raise 
      (StrobeKind.Kind_error 
         (sprintf "Expected kind %s, but got kind %s for type:\n%s"
            (string_of_kind expected_kind)
            (string_of_kind calculated_kind)
            (match s with STyp typ -> string_of_typ typ | SMult m -> string_of_mult m)))
  let kind_mismatch_typ t calc exp = kind_mismatch (STyp t) calc exp

  let rec well_formed_kind k = match k with
    | KMult (KStrobe (Strobe.KArrow _)) -> false
    | KMult k -> well_formed_kind k
    | KStrobe (Strobe.KEmbed k) -> well_formed_kind k
    | KStrobe Strobe.KStar -> true
    | KStrobe (Strobe.KArrow (args, ret)) -> 
      List.for_all (fun k -> match k with 
      | Strobe.KArrow _ -> false
      | Strobe.KStar -> true
      | Strobe.KEmbed k -> well_formed_kind k) args
      && well_formed_kind (KStrobe ret)

  let rec kind_check_sigma (env : env) (recIds : id list) (s : sigma) : kind = match s with
    | STyp t -> kind_check_typ env recIds t
    | SMult m -> kind_check_mult env recIds m

  and kind_check_typ (env : env) (recIds : id list) (typ : typ) : kind = match typ with
    | TStrobe t -> embed_k (StrobeKind.kind_check env recIds t)
    | TDom (_, t, sel) -> 
      let k = kind_check_typ env recIds t in
      if extract_k k <> Strobe.KStar then kind_mismatch_typ t k (KStrobe Strobe.KStar) else KStrobe Strobe.KStar
    | TForall (_, x, s, t) ->
      let k1 = kind_check_sigma env recIds s in
      let env' = match s with 
        | STyp t -> 
          let bs = try IdMap.find x env with Not_found -> [] in
          let bs = List.filter (fun b -> match extract_b b with Strobe.BTypBound _ -> false | _ -> true) bs in
          IdMap.add x ((BStrobe (Strobe.BTypBound(extract_t t, extract_k k1)))::bs) env
        | SMult m -> 
          let bs = try IdMap.find x env with Not_found -> [] in
          let bs = List.filter (fun b -> match embed_b (extract_b b) with BMultBound _ -> false | _ -> true) bs in
          IdMap.add x ((BMultBound(m, k1))::bs) env in
      let k2 = kind_check_typ env' recIds t in
      if k1 <> k2 then kind_mismatch_typ t k1 k2 else k1
    | TApp (t_op, s_args) ->
      begin 
        let check k_arg s_arg = 
          let k_actual = kind_check_sigma env recIds s_arg in
          if embed_k k_arg = k_actual then
            ()
          else 
            kind_mismatch s_arg k_actual (embed_k k_arg) in
        match t_op with
        (* | TPrim ("Constructing" as p) *)
        (* | TPrim ("Mutable" as p)  *)
        (* | TPrim ("Immutable" as p) -> *)
        (*   begin  *)
        (*     try List.iter2 check [KStar] s_args *)
        (*     with Invalid_argument _ -> raise (Kind_error (p ^ "<> expects one argument")) *)
        (*   end; *)
        (*   KStar *)
        | _ -> match extract_k (kind_check_typ env recIds t_op) with
          | Strobe.KArrow (k_args, k_result) ->
            begin 
              try
                List.iter2 check k_args s_args;
                embed_k k_result
              with Invalid_argument _ ->
                raise (StrobeKind.Kind_error
                         (sprintf "operator expects %d args, given %d"
                            (List.length k_args) (List.length s_args)))
            end
          | Strobe.KEmbed (KMult _)
          | Strobe.KStar ->
            raise (StrobeKind.Kind_error 
                     (sprintf "not a type operator:\n%s" (string_of_typ t_op)))
          | Strobe.KEmbed (KStrobe _) -> failwith "impossible: extract_k should've removed these wrappers"
      end

  and kind_check_mult env recIds (mult : multiplicity) = match mult with
    | MId x -> 
      begin 
        let rec unwrap b = match b with BStrobe (Strobe.BEmbed b) -> unwrap b | _ -> b in
        try 
          let bs = IdMap.find x env in
          let b = List.find (fun b -> match b with BMultBound _ -> true | _ -> false) (List.map unwrap bs) in
          (match b with
          | BMultBound (_, (KMult _ as k)) -> k
          | BMultBound (_, k) ->
            raise (StrobeKind.Kind_error (x ^ " is bound to MultBound(" ^ (string_of_kind k)
                               ^ "); that should be impossible!"))
          | BStrobe (Strobe.BTypBound (_, Strobe.KEmbed (KMult _ as k))) -> 
            raise (StrobeKind.Kind_error (x ^ " is bound to TypBound(" ^ (string_of_kind k) ^ "); that should be impossible!"))
          | BStrobe (Strobe.BTypBound (_, k)) ->
            raise (StrobeKind.Kind_error (x ^ " is bound to TypBound(" ^ (Strobe.string_of_kind k)
                               ^ "); expected KMult(_)"))
          | BStrobe (Strobe.BTermTyp _) ->
            raise (StrobeKind.Kind_error (x ^ " is a term variable, not a type variable"))
          | BStrobe (Strobe.BEmbed _) -> failwith "impossible: unwrap should've removed these wrappers")
        with Not_found ->
          if (not (List.mem x recIds)) then
            (* let strfmt = Format.str_formatter in *)
            (* let envText = (IdMap.iter (fun id k ->  *)
            (*   FormatExt.horz [FormatExt.text id; FormatExt.text "="; Pretty.kind k] strfmt; *)
            (*   Format.pp_print_newline strfmt () *)
            (* ) env); Format.flush_str_formatter() in *)
            let s = (sprintf "mult variable %s is unbound in env" x (* envText *)) in
            (* Printf.printf "%s" s; print_newline(); *)
            raise (StrobeKind.Kind_error s)
          else KMult (KStrobe Strobe.KStar)
      end
    | MZero m
    | MOne m
    | MZeroOne m
    | MOnePlus m
    | MZeroPlus m -> kind_check_mult env recIds m
    | MSum(m1, m2) ->
      let k1 = kind_check_mult env recIds m1 in
      let k2 = kind_check_mult env recIds m2 in
      if k1 <> k2 then 
        raise (StrobeKind.Kind_error ((string_of_mult mult) ^ " has inconsistently kinded components"))
      else k1
    | MPlain t -> kind_check_typ env recIds t

  let kind_check = kind_check_typ
end
