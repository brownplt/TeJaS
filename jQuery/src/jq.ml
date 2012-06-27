open Random
open Format
open FormatExt
open Prelude
open SetExt
module TestRealCSS = Css.TestRealCSS
open JQuery_syntax
open TypImpl
open JQuery_typechecking
module LS = LocalStructure
module TJSEnv = Typedjs_env

type arith = 
  | Var of int
  | Zero
  | Plus of arith * arith
  | Times of int * arith

let main () =
  Random.self_init();
  pp_set_margin std_formatter 120;
  pp_set_max_indent std_formatter 10000;
  let num_to_typ n t = match n with
    | -1 -> MZeroOne t
    | 0 -> MZero t
    | 1 -> MOne t
    | _ -> MOnePlus t in
  let rec arith_to_mult a = match a with
    | Var n -> MOne (MPlain (TId ("x_" ^ string_of_int n)))
    | Zero -> failwith "Broken!"
    | Plus (a1, a2) -> MSum (arith_to_mult a1, arith_to_mult a2)
    | Times (n, a2) -> num_to_typ n (arith_to_mult a2) in
  let rec cancel a = match a with
    | Var _ -> a
    | Zero -> a
    | Plus (a1, a2) -> begin match cancel a1, cancel a2 with
      | Zero, a2 -> a2
      | a1, Zero -> a1
      | a1, a2 -> Plus (a1, a2)
    end
    | Times (n, a2) -> begin match n with
      | 0 -> Zero
      | 1 -> cancel a2
      | _ -> match cancel a2 with
        | Zero -> Zero
        | a2 -> Times(n, a2)
    end in
  let rec arith depth = 
    if depth = 0 then Var (Random.int 10)
    else 
      if Random.bool ()
      then Plus (arith (depth-1), arith (depth-1))
      else Times ((Random.int 4) - 1, arith (depth-1)) in
  let rec print_arith a = match a with
    | Var n -> squish [text "x_"; int n]
    | Zero -> text "Zero"
    | Plus (n1, n2) -> horz [text "Plus"; parens [squish [print_arith n1; text ","];
                                                  print_arith n2]]
    | Times (n1, n2) -> horz [text "Times"; parens [squish [int n1; text ","];
                                                    print_arith n2]] in
  let rec eval a = match a with (* not quite true arithmetic eval -- times of negative numbers is weird *)
    | Var n -> 1
    | Zero -> 0
    | Plus (n1, n2) -> (eval n1) + (eval n2)
    | Times (n1, n2) -> (max 0 n1) * (eval n2) in
  let text t = text t std_formatter in
  let int n = int n std_formatter in
  let print_arith a = print_arith a std_formatter in
  let print_multiplicity m = Pretty.multiplicity m std_formatter in
  let print_typ t = Pretty.typ t std_formatter in
  let newline () = pp_print_newline std_formatter () in
  let flush () = pp_print_flush std_formatter () in
  let test1_help n a = 
    let e = eval a in
    let t = arith_to_mult a in
    text "Test "; int n; text ":"; newline ();
    text "Expr:      "; print_arith a; newline ();
    text "Canceled:  "; print_arith (cancel a); newline ();
    text "Min Count: "; int e; newline ();
    text "As type:   "; print_multiplicity t; newline ();
    text "Canonical: "; print_multiplicity (canonical_multiplicity t); newline (); newline (); flush () in
  let rec test1 n = if n = 0 then () else begin
      test1_help n (arith 6);
      test1 (n-1)
  end in
  let test2_help n a1 a2 = 
    let t1 = arith_to_mult a1 in
    let t2 = arith_to_mult a2 in
    let t1' = canonical_multiplicity t1 in
    let t2' = canonical_multiplicity t2 in
    let extract_typ m = match m with
      | MPlain t
      | MZero (MPlain t)
      | MOne (MPlain t)
      | MZeroOne (MPlain t)
      | MOnePlus (MPlain t)
      | MZeroPlus (MPlain t) -> t
      | _ -> failwith "impossible" in
    let t = TInter(None, extract_typ t1', extract_typ t2') in
    text "Test "; int n; text ":"; newline ();
    text "Expr1:     "; print_arith a1; newline ();
    text "Expr2:     "; print_arith a2; newline ();
    text "Canceled1: "; print_arith (cancel a1); newline ();
    text "Canceled2: "; print_arith (cancel a2); newline ();
    text "As type1:   "; print_multiplicity t1; newline ();
    text "As type2:   "; print_multiplicity t2; newline ();
    text "Canonical1: "; print_multiplicity t1'; newline ();
    text "Canonical2: "; print_multiplicity t2'; newline ();
    text "Inter:      "; print_typ (canonical_type t); newline (); newline (); flush () in
  let rec test2 n = if n = 0 then () else begin
    test2_help n (arith 6) (arith 6);
    test2 (n-1)
  end in
  let random_mult closed =
    let var = MId ("m_" ^ string_of_int (Random.int 10)) in
    let rec helper d = if d = 0 then (if closed then MPlain (TId ("t_" ^ string_of_int (Random.int 10))) else var)
    else match Random.int 6 with
      | 0 -> MZero (helper (d - 1))
      | 1 -> MOne (helper (d - 1))
      | 2 -> MZeroOne (helper (d - 1))
      | 3 -> MZeroPlus (helper (d - 1))
      | 4 -> MOnePlus (helper (d - 1))
      | _ -> MSum (helper (d - 1), helper (d - 1)) in
    helper in
  let test3_help n m1 m2 =
    let (_, free) = free_mult_ids m2 in
    try 
      let x = IdSet.choose free in
      let m3 = mult_mult_subst x m1 m2 in
      text "Test "; int n; text ":"; newline ();
      text "M1:                    "; print_multiplicity m1; newline ();
      text "M2:                    "; print_multiplicity m2; newline ();
      text "Canonical M1:          "; print_multiplicity (canonical_multiplicity m1); newline ();
      text "Canonical M2:          "; print_multiplicity (canonical_multiplicity m2); newline ();
      text "M2[M1/`"; text x; text "]:           "; print_multiplicity m3; newline (); 
      text "Canonical M2[M1/`"; text x; text "]: "; print_multiplicity (canonical_multiplicity m3);
      newline (); newline ()
    with Not_found -> () in
  let rec test3 n = if n = 0 then () else begin
    test3_help n (random_mult true 3) (random_mult false 6);
    test3 (n-1)
  end in
  let test4 () = begin
    (*
      let f = jQ<1+<'a>> -> 1<'a> in
      let g = 1<'a> in
      f g :: 1<'a>
    *)
    let p = Pos.dummy in 
    let open Exp in
    let open JQuery_env in
    let txt = "type jqFirst = ['jQ<1+<'a>>] => 'jQ<1<'a>>
               type jqOneA = 'jQ<1<'a>>
               type jqZerooneB = 'jQ<01<'b>>" in
    let env = TJSEnv.parse_env txt "Test env" in
    let rec print_decl d =
      let open Typedjs_syntax in
      let open Format in
      let open FormatExt in
      let open WritTyp in
      match d with
      | EnvBind(_, id, t) -> label (id ^ " : ") [print_typ t]
      | EnvType(_, id, t) -> label (id ^ " = ") [print_typ t]
      | EnvPrim(_, id) -> horz[text "Prim"; text id]
      | RecBind ds -> begin match ds with
        | [] -> failwith "impossible"
        | [d] -> label "rec " [print_decl d]
        | d::ds -> vert ((horz[text "rec"; print_decl d])::(List.map (fun d -> horz[text "and"; print_decl d]) ds))
      end
      | ObjectTrio (_, (c, ct), (p, pt), (i, it)) ->
        vert[horz[text "constructor"; text c; text "="; print_typ ct];
             horz[text "prototype"; text p; text "="; print_typ pt];
             horz[text "instance"; text i; text "="; print_typ it]] in
    vert (List.map print_decl env) Format.std_formatter; Format.print_newline();
    let doLet x b e = ELet(p, x, b, e) in
    let cheatTyp t = ECheat(p, t, EConst(p, "")) in
    let tDom = TDom(None, TId "a", Css.all) in
    let exp = 
      doLet "f" (cheatTyp (TArrow(None,
                                  [TApp(TId("jQ"), [SMult (MOnePlus (MPlain (tDom)))])], None,
                                  TApp(TId("jQ"), [SMult (MOne (MPlain (TId "a")))]))))
        (doLet "g" (cheatTyp (TApp(TId("jQ"), [SMult (MOne (MPlain (TId "a")))])))
           (EApp(p, EId(p, "f"), [EId (p, "g")]))) in
    let retTyp = (TApp(TId("jQ"), [SMult (MZeroOne (MPlain (TId "b")))])) in
    let env = (unchecked_bind_typ_ids [("a", TId "b")] empty_env) in
    begin try
      text "Typechecking: Is"; newline ();
      JQuery_syntax.Pretty.exp exp std_formatter; text " : "; print_typ retTyp; newline ();
      text "in environment"; newline ();
      braces (print_env env) std_formatter; text "?"; newline ();
      with_typ_exns (fun () -> check env None exp retTyp);
      text "Succeeded"; newline ();
    with Typ_error(p, e) -> (text "FAILED: "; text e; newline ()) end;
    text "Cache hits:   "; int !JQuery_subtyping.cache_hits; newline ();
    text "Cache misses: "; int !JQuery_subtyping.cache_misses; newline ();
    (* JQuery_subtyping.print_cache "Cache is: " std_formatter; newline() *)
  end in
  let test5 () = begin
    let text = "(Tweet : \"\"\"A structure for tweets\"\"\"
                   DivElement
                   optional classes = [first, last]
                   classes = [tweet]
                   /* ignore this! */
                   (Author : DivElement classes = [author] ...)
                   (Time : DivElement classes = [time] )
                   (Content : DivElement classes = [content] ... <Other> ...)
                   ...
               )" in
    let decls = LS.parseLocalStructure text in
    List.map (fun d -> LS.Pretty.p_decl d Format.std_formatter; Format.print_newline()) decls
  end in
  (* test1 500; *)
  (* test2 500 *)
  (* test3 100; *)
  test4 ();
  (* Printf.printf "All CSS succeeded: %b\n" (TestRealCSS.testSels 1000); *)
  test5 ()
;;

main ()
      
      
  
