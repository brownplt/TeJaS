open Random
open Format
open FormatExt
open Prelude
open SetExt
module TestRealCSS = Css.TestRealCSS
open JQuery_syntax
module JQ = JQueryImpl
module S = StrobeImpl

(* open JQuery_typechecking *)
module Desugar = Typedjs_desugar.Make (StrobeMod) (JQueryMod)
module TJSEnv = Typedjs_env.Make (StrobeMod) (Strobe_kind) (Desugar)
module JQEnv = JQuery_env.MakeExt (JQueryMod) (JQuery_kind) (TJSEnv)
module LJSfromEJS = Typedjs_fromExpr.Make (Exp)
module WeaveAnnotations = WeaveAnnotations.Make (Exp) (Desugar)

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
    | -1 -> JQ.MZeroOne t
    | 0 -> JQ.MZero t
    | 1 -> JQ.MOne t
    | _ -> JQ.MOnePlus t in
  let rec arith_to_mult a = match a with
    | Var n -> JQ.MOne (JQ.MPlain (JQ.TStrobe (S.TId ("x_" ^ string_of_int n))))
    | Zero -> failwith "Broken!"
    | Plus (a1, a2) -> JQ.MSum (arith_to_mult a1, arith_to_mult a2)
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
  let print_multiplicity m = JQuery.Pretty.multiplicity m std_formatter in
  let print_typ t = JQuery.Pretty.typ t std_formatter in
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
    text "Canonical: "; print_multiplicity (JQuery.canonical_multiplicity t); newline (); newline (); flush () in
  let rec test1 n = if n = 0 then () else begin
      test1_help n (arith 6);
      test1 (n-1)
  end in
  let test2_help n a1 a2 = 
    let t1 = arith_to_mult a1 in
    let t2 = arith_to_mult a2 in
    let t1' = JQuery.canonical_multiplicity t1 in
    let t2' = JQuery.canonical_multiplicity t2 in
    let extract_typ m = match m with
      | JQ.MPlain t
      | JQ.MZero (JQ.MPlain t)
      | JQ.MOne (JQ.MPlain t)
      | JQ.MZeroOne (JQ.MPlain t)
      | JQ.MOnePlus (JQ.MPlain t)
      | JQ.MZeroPlus (JQ.MPlain t) -> t
      | _ -> failwith "impossible" in
    let t = JQ.TStrobe (S.TInter(None, S.TEmbed (extract_typ t1'), S.TEmbed (extract_typ t2'))) in
    text "Test "; int n; text ":"; newline ();
    text "Expr1:     "; print_arith a1; newline ();
    text "Expr2:     "; print_arith a2; newline ();
    text "Canceled1: "; print_arith (cancel a1); newline ();
    text "Canceled2: "; print_arith (cancel a2); newline ();
    text "As type1:   "; print_multiplicity t1; newline ();
    text "As type2:   "; print_multiplicity t2; newline ();
    text "Canonical1: "; print_multiplicity t1'; newline ();
    text "Canonical2: "; print_multiplicity t2'; newline ();
    text "Inter:      "; print_typ (JQuery.canonical_type t); newline (); newline (); flush () in
  let rec test2 n = if n = 0 then () else begin
    test2_help n (arith 6) (arith 6);
    test2 (n-1)
  end in
  let random_mult closed =
    let var = JQ.MId ("m_" ^ string_of_int (Random.int 10)) in
    let rec helper d = if d = 0 then (if closed then JQ.MPlain (JQ.TStrobe (S.TId ("t_" ^ string_of_int (Random.int 10)))) else var)
    else match Random.int 6 with
      | 0 -> JQ.MZero (helper (d - 1))
      | 1 -> JQ.MOne (helper (d - 1))
      | 2 -> JQ.MZeroOne (helper (d - 1))
      | 3 -> JQ.MZeroPlus (helper (d - 1))
      | 4 -> JQ.MOnePlus (helper (d - 1))
      | _ -> JQ.MSum (helper (d - 1), helper (d - 1)) in
    helper in
  let test3_help n m1 m2 =
    let free = JQuery.free_mult_ids m2 in
    try 
      let x = IdSet.choose free in
      let m3 = JQuery.mult_mult_subst x m1 m2 in
      text "Test "; int n; text ":"; newline ();
      text "M1:                    "; print_multiplicity m1; newline ();
      text "M2:                    "; print_multiplicity m2; newline ();
      text "Canonical M1:          "; print_multiplicity (JQuery.canonical_multiplicity m1); newline ();
      text "Canonical M2:          "; print_multiplicity (JQuery.canonical_multiplicity m2); newline ();
      text "M2[M1/`"; text x; text "]:           "; print_multiplicity m3; newline (); 
      text "Canonical M2[M1/`"; text x; text "]: "; print_multiplicity (JQuery.canonical_multiplicity m3);
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
    (* let p = Pos.dummy in *)
    let open JQuery_syntax.Exp in
    let open JQuery_env in
    let txt = "type jqFirst = ['jQ<1+<'a>>] => 'jQ<1<'a>>
               type jqOneA = 'jQ<1<'a>>
               type jqZerooneB = 'jQ<01<'b>>" in
    let env = JQEnv.parse_env txt "Test env" in
    let exp = "/*:: type DOM = { name : Str }; */
               /*:: type aDom = { name : /a/ }; */
               /*:: type abDom = { name : /a|b/ }; */
               var f = /*: cheat ([jQ<1+<DOM>>] => jQ<1<aDom>>) */0;
               var g = /*: cheat jQ<1<aDom>> */0;
               var ret = /*: jQ<1<abDom>>*/(f(g));
               " in
    let js = JavaScript.parse_javascript exp "<test>" in
    let rec helper env d = 
      let open Typedjs_writtyp.WritTyp in
      match d with
      | EnvBind (_, x, _)
      | EnvType (_, x, _)
      | EnvPrim (_, x) -> IdMap.add x d env
      | RecBind ds -> List.fold_left helper env ds
      | ObjectTrio (_, (x, _), (y, _), (z, _)) ->
        IdMap.add x d (IdMap.add y d (IdMap.add x d env)) in
    let env' = List.fold_left helper IdMap.empty env in
    let new_decls = ReadTyps.new_decls (List.rev !JavaScript_lexer.comments) in
    let rec helper recIds env d = 
      let open Typedjs_writtyp.WritTyp in
      match d with
      | EnvType(p, x, t) -> 
        let t' = Desugar.desugar_typ p t in
        let t'' = squash env t' in
        (bind_rec_typ_id x recIds (TypImpl.replace_name (Some x) t'') env)
      | ObjectTrio _ -> JQEnv.extend_global_env env [d]
      | RecBind binds ->
        let ids = List.concat (List.map (fun b -> match b with
          | EnvBind (_, x, _) -> [x]
          | EnvType (_, x, _) -> [x]
          | ObjectTrio(_, (c, _), (p, _), (i, _)) -> [c;p;i]
          | EnvPrim _
          | RecBind _ -> []) binds) in
        List.fold_left (helper ids) env binds
      | _ -> env in
    let env' = List.fold_left (helper []) env' new_decls in
    let tjs = LJSfromEJS.from_exprjs env' (Exprjs.lift_decls (Exprjs_syntax.from_javascript js)) in
    let annot = 
      let typ_db = ReadTyps.read_typs js (List.rev !JavaScript_lexer.comments) in
      WeaveAnnotations.weave typ_db tjs in
    Exp.Pretty.exp annot std_formatter;
    print_newline()
    (*   doLet "f" (cheatTyp (TArrow(None, *)
    (*                               [TApp(TId("jQ"), [SMult (MOnePlus (MPlain (tDom)))])], None, *)
    (*                               TApp(TId("jQ"), [SMult (MOne (MPlain (TId "a")))])))) *)
    (*     (doLet "g" (cheatTyp (TApp(TId("jQ"), [SMult (MOne (MPlain (TId "a")))]))) *)
    (*        (EApp(p, EId(p, "f"), [EId (p, "g")]))) in *)
    (* let retTyp = (TApp(TId("jQ"), [SMult (MZeroOne (MPlain (TId "b")))])) in *)
    (* let env = (unchecked_bind_typ_ids [("a", TId "b")] empty_env) in *)
    (* begin try *)
    (*   text "Typechecking: Is"; newline (); *)
    (*   JQuery_syntax.Pretty.exp exp std_formatter; text " : "; print_typ retTyp; newline (); *)
    (*   text "in environment"; newline (); *)
    (*   braces (print_env env) std_formatter; text "?"; newline (); *)
    (*   with_typ_exns (fun () -> check env None exp retTyp); *)
    (*   text "Succeeded"; newline (); *)
    (* with Typ_error(p, e) -> (text "FAILED: "; text e; newline ()) end; *)
    (* text "Cache hits:   "; int !JQuery_subtyping.cache_hits; newline (); *)
    (* text "Cache misses: "; int !JQuery_subtyping.cache_misses; newline (); *)
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
  (* test2 500; *)
  (* test3 100; *)
  test4 ();
  (* Printf.printf "All CSS succeeded: %b\n" (TestRealCSS.testSels 1000); *)
  test5 ()
;;

main ()
      
      
  
