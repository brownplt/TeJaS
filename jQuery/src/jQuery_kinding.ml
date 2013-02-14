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
      
  let list_prims = StrobeKind.list_prims
  let new_prim_typ = StrobeKind.new_prim_typ

  let kind_mismatch s calculated_kind expected_kind = 
    raise 
      (Strobe.Kind_error 
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
      && well_formed_kind (embed_k ret)

  let short_string_of_typ t =
    let open Format in
    let max = pp_get_max_boxes str_formatter () in
    pp_set_max_boxes str_formatter 15;
    let s = string_of_typ t in
    pp_set_max_boxes str_formatter max;
    s

  let trace (msg : string) print success (thunk : 'a -> 'b) (arg : 'a) = 
    thunk arg
    (* Strobe.trace msg (print arg) success (fun () -> thunk arg)  *)

  let rec kind_check_sigma (env : env) (recIds : id list) (s : sigma) : kind = match s with
    | STyp t -> kind_check_typ env recIds t
    | SMult m -> kind_check_mult env recIds m

  and kind_check_typ (env : env) (recIds : id list) (typ : typ) : kind = 
    trace "KindCheckTyp" short_string_of_typ (fun _ -> true) (fun typ -> kind_check_typ' env recIds typ) typ

  and kind_check_typ' (env : env) (recIds : id list) (typ : typ) : kind = 
    let bind_kind_id x k env = 
      let bs = try IdMap.find x env with Not_found -> [] in
      let bs = List.filter (fun b -> match extract_b b with Strobe.BTyvar _ -> false | _ -> true) bs in
      IdMap.add x ((embed_b (Strobe.BTyvar (extract_k k)))::bs) env in
    match typ with
    | TStrobe t -> embed_k (StrobeKind.kind_check env recIds t)
    | TDom (_,_, t, sel) -> 
      let k = kind_check_typ env recIds t in
      if extract_k k <> Strobe.KStar then kind_mismatch_typ t k (KStrobe Strobe.KStar) else KStrobe Strobe.KStar
    | TLambda (_, args, t) ->
      let env' = fold_right (fun (x, k) env -> bind_kind_id x k env) args env in
      KStrobe (Strobe.KArrow (List.map (fun (_, k) -> extract_k k) args, extract_k (kind_check_typ env' recIds t)))
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
      k2
    | TApp (t_op, s_args) ->
      begin 
        let check k_arg s_arg = 
          let k_actual = kind_check_sigma env recIds s_arg in
          if k_arg = extract_k k_actual then
            ()
          else begin
            kind_mismatch s_arg k_actual (embed_k k_arg)
          end in
        match extract_t t_op with
        | Strobe.TPrim ("childrenOf" as p)
        | Strobe.TPrim ("parentOf" as p)
        | Strobe.TPrim ("nextSibOf" as p)
        | Strobe.TPrim ("prevSibOf" as p)
        | Strobe.TPrim ("findOf" as p)
        | Strobe.TPrim ("parentsOf" as p)
        | Strobe.TPrim ("prevAllOf" as p)
        | Strobe.TPrim ("nextAllOf" as p)
        | Strobe.TPrim ("oneOf" as p) ->
          begin
            try List.iter2 check [Strobe.KEmbed (KMult (KStrobe Strobe.KStar))] s_args
            with Invalid_argument _ -> 
              raise (Strobe.Kind_error 
                       (sprintf "%s<> expects one argument, got %d" 
                          p (List.length s_args)))
          end;
          KMult (KStrobe Strobe.KStar)
        | Strobe.TPrim ("selector" as p) ->
          begin
            try List.iter2 check [Strobe.KStar] s_args
            with Invalid_argument _ ->
              raise (Strobe.Kind_error
                       (sprintf "%s<> expects one argument, got %d"
                          p (List.length s_args)))
          end;
          KStrobe Strobe.KStar       
        | Strobe.TPrim ("filterSel" as p) ->
          begin
            try List.iter2 check [Strobe.KEmbed (KMult (KStrobe Strobe.KStar)); Strobe.KStar] s_args
            with Invalid_argument _ ->
              raise (Strobe.Kind_error
                       (sprintf "%s<> expects two arguments, got %d"
                          p (List.length s_args)))
          end;
          KMult (KStrobe Strobe.KStar)
        | _ -> match extract_k (kind_check_typ env recIds t_op) with
          | Strobe.KArrow (k_args, k_result) ->
            begin 
              try
                List.iter2 check k_args s_args;
                embed_k k_result
              with Invalid_argument _ ->
                raise (Strobe.Kind_error
                         (sprintf "operator expects %d args, given %d"
                            (List.length k_args) (List.length s_args)))
            end
          | Strobe.KEmbed (KMult _)
          | Strobe.KStar ->
            raise (Strobe.Kind_error 
                     (sprintf "not a type operator:\n%s" (string_of_typ t_op)))
          | Strobe.KEmbed (KStrobe _) -> failwith "impossible: extract_k should've removed these wrappers"
      end

  and kind_check_mult (env : env) (recIds : id list) (mult : multiplicity) : kind = 
    trace "KindCheckMult" string_of_mult (fun _ -> true) (fun mult -> kind_check_mult' env recIds mult) mult

  and kind_check_mult' env recIds (mult : multiplicity) = match mult with
    | MId x -> 
      begin 
        try 
          let bs = IdMap.find x env in
          let b = List.find (fun b -> match b with 
            | BMultBound _ | BStrobe (Strobe.BTyvar _)-> true | _ -> false) (List.map unwrap_b bs) in
          (match b with
          | BStrobe (Strobe.BTyvar k) -> embed_k k
          | BMultBound (_, ((KMult _) as k)) -> k
          | BMultBound (_, k) ->
            raise (Strobe.Kind_error (x ^ " is bound to MultBound(" ^ (string_of_kind k)
                               ^ "); that should be impossible!"))
          | BStrobe _ -> failwith "impossible: List.find can only find a BMultBound here"
          )
        with Not_found ->
          if (not (List.mem x recIds)) then
            let envText = FormatExt.to_string (fun e -> FormatExt.braces (Strobe.Pretty.env e)) env in
            let s = (sprintf "mult variable %s is unbound in env %s" x envText) in
            (* Printf.eprintf "%s" s; *)
            raise (Strobe.Kind_error s)
          else KMult (KStrobe Strobe.KStar)
      end
    | MZero m
    | MOne m
    | MZeroOne m
    | MOnePlus m
    | MZeroPlus m -> begin match kind_check_mult env recIds m with
      | KMult (KStrobe Strobe.KStar)
      | KStrobe Strobe.KStar -> KMult (KStrobe Strobe.KStar)
      | k -> raise (Strobe.Kind_error ((string_of_mult mult) ^ " is ill-formed with kind " ^ (string_of_kind k)))
    end
    | MSum(m1, m2) ->
      let k1 = kind_check_mult env recIds m1 in
      let k2 = kind_check_mult env recIds m2 in
      if k1 <> k2 then 
        raise (Strobe.Kind_error ((string_of_mult mult) ^ " has inconsistently kinded components"))
      else k1
    | MPlain t -> kind_check_typ env recIds t

  let kind_check = kind_check_typ
end
