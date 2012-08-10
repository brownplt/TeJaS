open Random
open Format
open FormatExt
open Prelude
open SetExt
module TestRealCSS = Css.TestRealCSS
open JQuery_syntax
module JQ = JQuery
module S = StrobeImpl

module Desugar = Typedjs_desugar.Make (StrobeMod) (JQueryMod)
module SEnv = Strobe_env.Make (StrobeMod) (Strobe_kind) (Desugar)
module JQEnv = JQuery_env.MakeExt (JQueryMod) (JQuery_kind) (SEnv) (Desugar)
module rec JQuerySub : (JQuery_sigs.JQUERY_SUBTYPING
                        with type typ = JQueryImpl.typ
  with type kind = JQueryImpl.kind
  with type multiplicity = JQueryImpl.multiplicity
  with type sigma = JQueryImpl.sigma
  with type binding = JQueryImpl.binding
  with type env = JQueryImpl.env
  with type baseTyp = JQueryImpl.baseTyp
  with type baseKind = JQueryImpl.baseKind
  with type baseBinding = JQueryImpl.baseBinding) =
  JQuery_subtyping.MakeActions (StrobeSub) (JQueryMod) (JQEnv)
and StrobeSub : (Strobe_sigs.STROBE_SUBTYPING
                 with type typ = StrobeImpl.typ
  with type kind = StrobeImpl.kind
  with type binding = StrobeImpl.binding
  with type extTyp = StrobeImpl.extTyp
  with type extKind = StrobeImpl.extKind
  with type extBinding = StrobeImpl.extBinding
  with type pat = StrobeImpl.pat
  with type obj_typ = StrobeImpl.obj_typ
  with type presence = StrobeImpl.presence
  with type env = StrobeImpl.env) =
  Strobe_subtyping.MakeActions (StrobeMod) (JQuerySub) (JQEnv)

module DummySemicfa = struct
  type env = JQEnv.env
  type exp = Exp.exp
  let semicfa _ _ e = e
end
module DummyStatic = struct
  type typ = JQEnv.typ
  type env = JQEnv.env
  let static _ _ t = t
end

module rec StrobeTC : (Strobe_sigs.STROBE_TYPECHECKING
                with type typ = StrobeImpl.typ
  with type kind = StrobeImpl.kind
  with type binding = StrobeImpl.binding
  with type extTyp = StrobeImpl.extTyp
  with type extKind = StrobeImpl.extKind
  with type extBinding = StrobeImpl.extBinding
  with type pat = StrobeImpl.pat
  with type obj_typ = StrobeImpl.obj_typ
  with type presence = StrobeImpl.presence
  with type env = StrobeImpl.env
  with type exp = Exp.exp) =
  Strobe_typechecking.Make (StrobeMod) (Exp) (JQEnv) (StrobeSub) (JQuery_kind) (DummySemicfa) (DummyStatic) (JQueryTC)
and JQueryTC : (JQuery_sigs.JQUERY_TYPECHECKING
                       with type typ = JQueryImpl.typ
  with type kind = JQueryImpl.kind
  with type multiplicity = JQueryImpl.multiplicity
  with type sigma = JQueryImpl.sigma
  with type binding = JQueryImpl.binding
  with type env = JQueryImpl.env
  with type baseTyp = JQueryImpl.baseTyp
  with type baseKind = JQueryImpl.baseKind
  with type baseBinding = JQueryImpl.baseBinding
  with type exp = Exp.exp) =
  JQuery_typechecking.Make (JQueryMod) (Exp) (JQEnv) (JQuerySub) (JQuery_kind) (StrobeTC)

type arith = 
  | Var of int
  | Zero
  | Plus of arith * arith
  | Times of int * arith
let num_to_typ n t = match n with
  | -1 -> JQ.MZeroOne t
  | 0 -> JQ.MZero t
  | 1 -> JQ.MOne t
  | _ -> JQ.MOnePlus t
let rec arith_to_mult a = match a with
  | Var n -> JQ.MOne (JQ.MPlain (JQ.TStrobe (S.TPrim ("x_" ^ string_of_int n))))
  | Zero -> failwith "Broken!"
  | Plus (a1, a2) -> JQ.MSum (arith_to_mult a1, arith_to_mult a2)
  | Times (n, a2) -> num_to_typ n (arith_to_mult a2)
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
  end
let rec arith depth = 
  if depth = 0 then Var (Random.int 10)
  else 
    if Random.bool ()
    then Plus (arith (depth-1), arith (depth-1))
    else Times ((Random.int 4) - 1, arith (depth-1))
let rec print_arith a = match a with
  | Var n -> squish [text "x_"; int n]
  | Zero -> text "Zero"
  | Plus (n1, n2) -> horz [text "Plus"; parens [squish [print_arith n1; text ","];
                                                print_arith n2]]
  | Times (n1, n2) -> horz [text "Times"; parens [squish [int n1; text ","];
                                                  print_arith n2]]
let rec eval a = match a with (* not quite true arithmetic eval -- times of negative numbers is weird *)
  | Var n -> 1
  | Zero -> 0
  | Plus (n1, n2) -> (eval n1) + (eval n2)
  | Times (n1, n2) -> (max 0 n1) * (eval n2)

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
  helper


let text t = text t std_formatter
let int n = int n std_formatter
let print_arith a = print_arith a std_formatter
let print_multiplicity m = JQuery.Pretty.multiplicity m std_formatter
let print_typ t = JQuery.Pretty.typ t std_formatter
let newline () = pp_print_newline std_formatter ()
let flush () = pp_print_flush std_formatter ()


let print_env env : unit =
  JQEnv.print_env env std_formatter;
  Format.print_newline ()


exception STest_failure of string

(* Helper: consumes a list of functions that return exception option lists,
   executes them in order, and raises the first exception it finds. 
   Otherwise produces unit *)
let raise_exns (fs : (_ -> exn option list) list) : unit =
  let all_exn_strings = 
    (List.fold_left (fun acc f ->
      let exns =  f() in 
      let exns_strings =
        ListExt.filter_map
        (fun eo -> match eo with
        | Some exn -> Some (Printexc.to_string exn)
        | None -> None) exns in
      List.append acc exns_strings) [] fs) in

  match all_exn_strings with 
  | [] -> ()
  | _ -> raise (STest_failure (String.concat ",\n" all_exn_strings))

let test_harness test fail_msg =
  let margin = pp_get_margin std_formatter () in
  let max_indent = pp_get_max_indent std_formatter () in
  try
    pp_set_margin std_formatter 120;
    pp_set_max_indent std_formatter 10000;
    test ();
    [None]
  with e -> 
    pp_set_margin std_formatter margin;
    pp_set_max_indent std_formatter max_indent;
    let emsg = Printexc.to_string e in
    Printf.eprintf "\n%s, \nEXCEPTION: %s\n" fail_msg emsg;
    [Some e]


let test_harness_many (tests : (( int -> string) * ( _ -> unit )) list)
    : exn option list =
  
  let foldi (f : int -> 'b -> 'a -> 'b) (s : 'b) (l : 'a list) : 'b = 
    let rec helper n a l =
      match l with
      | [] -> a
      | hd::tl ->  
        helper (n+1) (f n a hd) tl in
    helper 0 s l in

  (* let iteri (f : int -> 'a -> unit) (l : 'a list) : unit = *)
  (*   let rec helper n l = *)
  (*     match l with *)
  (*     | [] -> () *)
  (*     | hd::tl -> f n hd; helper (n+1) tl in *)
  (*   helper 0 l in                        *)
  
  foldi (fun n exns (f_msg, f_test) -> 
    (List.append (test_harness f_test (f_msg n)) exns)) [] tests


(************************** Testing helper functions **************************)

module Helper = struct    

(* Helper: creates a sel from a list of selectors *)
  let sel sels = 
    let module Css = JQueryMod.Css in
    match sels with 
    | [] -> failwith "shouldn't be providing an empty selector"
    | [s] -> Css.singleton s
    | hd::tl -> 
      List.fold_left (fun sels s -> Css.union (Css.singleton s) sels)
        (Css.singleton hd) tl


  let tdom id typ_string sel_strings = 
    JQ.TDom (None, 
             id, 
             JQ.TStrobe (Strobe.TId ((String.capitalize typ_string) ^ "Element")),
             sel sel_strings)

  (* Helper that turns two JQ.typs into a TStrobe Strobe.TUnion *)
  let tu t1 t2 = 
    JQ.embed_t (S.TUnion (None, (JQ.extract_t t1), (JQ.extract_t t2))) 

  let tid id = JQ.embed_t (Strobe.TId id)

  let env = 
    let raw = 
      "type Element = #{ name : Str };
       type DivElement = #{ name : /\"HTMLDivElement\"/ };" in

    let decls = JQEnv.parse_env raw "Helper env" in
    
    JQEnv.extend_global_env IdMap.empty decls
  
    

end



(********************************* Tests **************************************)


(* DEPENDS on working extend_global_env *)
let expose_tdoms_test () =
 
  let module H = Helper in

  let raw_decls = 
   " (Tweet : div classes=[tweet])" in
  

  let decls = JQEnv.parse_env raw_decls "Expose TDoms test" in

  let env = JQEnv.extend_global_env H.env decls in

  let wrapper t pass = (fun _ ->

    try 
      ignore( JQEnv.expose_tdoms env t);
      if (not pass) 
      then raise 
        (STest_failure (sprintf "%s SHOULD have caused an error when being exposed"
                          (JQ.string_of_typ t)))
      else ()
    with Strobe.Typ_error _ -> 
      if pass then begin
        raise (STest_failure 
           (sprintf "%s should NOT have caused an error when being exposed"
              (JQ.string_of_typ t))) end
      else () )

  in (* END of wrapper *)

  
  let fmsg d n = (sprintf "Expose TDom test #%n failed.\nDescription: %s"n d) in

  test_harness_many [

    ((fmsg "Basic TDom"),
     wrapper (H.tdom "Tweet" "div" ["*"]) true);

    ((fmsg "TId that resolves to a TDom"),
     wrapper (JQ.embed_t (S.TId "Tweet")) true);

    ((fmsg "TId that does NOT resolve to a TDom"),
     wrapper (JQ.embed_t (S.TId "DivElement")) false);

    ((fmsg "Element is ok at the moment"),
     wrapper (JQ.embed_t (S.TId "Element")) true);

    ((fmsg "TUnion of TDoms with ids that resolve to a TDom"),
     wrapper (H.tu 
                (H.tdom "Tweet" "div" ["*"])
                (H.tu
                   (H.tu
                      (H.tdom "Tweet" "div" ["*"])
                      (H.tid "Tweet"))
                   (H.tid "Tweet"))) true);

    ((fmsg "TUnion of TDoms that contain an id that does NOT resolve to a TDom"),
     wrapper (H.tu
                (H.tu
                   (H.tdom "Tweet" "div" ["*"])
                   (H.tid "DivElement"))
                (H.tid "Tweet")) false);

    ((fmsg "Some non-TDom JQ.typ"),
     wrapper (JQ.TApp ((H.tdom "Tweet" "div" ["*"]),
                       [JQ.SMult (JQ.MOne (JQ.MPlain (H.tid "Tweet")))]))
       false);

    ((fmsg "Some non-TDom Strobe.typ"),
     wrapper (JQ.embed_t S.TBot) false);

  ]
(* END of extract_tdom_test *)

(* DEPENDS on working extend_global_env *)
let subtyping_test () = 

  let module H = Helper in

  let raw_env = 
    "(Tweet1 : div classes=[tweet]
       (Author : div classes=[author])
       (Content1 : div classes=[content1])
       (Time : div classes=[time]));
     (Tweet2 : div classes=[tweet]
       (Content2 : div classes=[content2]));
     (Tweet3: div classes=[tweet])" in

  let decls  = (JQEnv.parse_env raw_env "Subtyping test") in

  let env = JQEnv.extend_global_env H.env decls in

  let wrapper t1 t2 pass = 
    (fun _ -> 
      match (JQuerySub.subtype_typ true env t1 t2), pass with
      | true, true
      | false, false -> ()
      | true, false -> raise 
        (STest_failure (sprintf "%s should NOT subtype %s, but it does"
                          (JQ.string_of_typ t1) (JQ.string_of_typ t2)))
      | false, true -> raise 
        (STest_failure (sprintf "%s SHOULD subtype %s, but it does not"
                          (JQ.string_of_typ t1) (JQ.string_of_typ t2)))) in


  let fmsg d n = (sprintf "Subtyping test %n failed.\nDescription: %s"n d) in

  test_harness_many [

    (*** TDom subtyping tests ***)
    
    ((fmsg "DivElement <: DivElement"),
     (wrapper 
       (H.tdom "Tweet1" "div" ["*"])
       (H.tdom "Tweet1" "div" ["*"])
       true));

    ((fmsg "DivElement <: Element"),
     (wrapper 
       (H.tdom "Tweet1" "div" ["*"])
       (H.tdom "Tweet1" "" ["*"])
       true));

    ((fmsg "Element </: DivElement"),
     (wrapper 
       (H.tdom "Tweet1" "" ["*"])
       (H.tdom "Tweet1" "div" ["*"])
       false));

    ((fmsg "Tweet1 <: Tweet2"),
     (wrapper 
       (H.tdom "Tweet1" "div" ["*"])
       (H.tdom "Tweet2" "div" ["*"])
       true));

    ((fmsg "Tweet2 <: Tweet1"),
     (wrapper 
       (H.tdom "Tweet2" "div" ["*"])
       (H.tdom "Tweet1" "div" ["*"])
       true));

    ((fmsg "TDom <: TUnion"),
     (wrapper
        (H.tdom "Tweet1" "div" ["*"])
        (H.tu
           (H.tdom "Tweet2" "div" ["*"])
           (H.tdom "Tweet3" "div" ["*"]))
       true));

    ((fmsg "TDom </: TUnion"),
     (wrapper
        (H.tdom "Tweet1" "div" ["*"])
        (H.tu
           (H.tdom "Author" "div" ["*"])
           (H.tdom "Content1" "div" ["*"]))
       false));

    ((fmsg "TDom </: TUnion t2"),
     (wrapper
        (H.tdom "Tweet1" "" ["*"])
        (H.tu
           (H.tdom "Tweet2" "div" ["*"])
           (H.tdom "Tweet3" "div" ["*"]))
       false));

    ((fmsg "TUnion <: TDom"),
     (wrapper 
        (H.tu 
           (H.tdom "Tweet2" "div" ["*"])
           (H.tdom "Tweet3" "div" ["*"]))
        (H.tdom "Tweet1" "div" ["*"])
        true));


    ((fmsg "TUnion </: TDom t1"),
     (wrapper 
        (H.tu 
           (H.tdom "Tweet1" "div" ["*"])
           (H.tdom "Content1" "div" ["*"]))
        (H.tdom "Tweet1" "div" ["*"])
        false));

    ((fmsg "TUnion </: TDom t2"),
     (wrapper 
        (H.tu 
           (H.tdom "Author" "div" ["*"])
           (H.tdom "Tweet1" "div" ["*"]))
        (H.tdom "Tweet1" "div" ["*"])
        false));

    ((fmsg "TUnion </: TDom t3"),
     (wrapper 
        (H.tu 
           (H.tdom "Author" "div" ["*"])
           (H.tdom "Content1" "div" ["*"]))
        (H.tdom "Tweet1" "div" ["*"])
        false));

    ((fmsg "TUnion <: TUnion t1"),
     (wrapper 
        (H.tu 
           (H.tdom "Author" "div" ["*"])
           (H.tdom "Content1" "div" ["*"]))
        (H.tu 
           (H.tdom "Author" "div" ["*"])
           (H.tdom "Content1" "div" ["*"]))
        true));

    ((fmsg "inter1 <: inter2 t1"),
     (wrapper 
       (H.tdom "Tweet1" "div" ["p"])
       (H.tdom "Tweet1" "div" ["div"])
       true));

    ((fmsg "inter1 <: inter2 t2"),
     (wrapper 
       (H.tdom "Tweet1" "div" [".tweet"])
       (H.tdom "Tweet2" "div" ["*"])
       true));

    ((fmsg "inter1 <: inter2 t3"),
     (wrapper 
       (H.tdom "Author" "div" [".tweet"])
       (H.tdom "Content2" "div" [".tweet"])
       true));

    ((fmsg "inter1 </: inter2 t1"),
     (wrapper 
       (H.tdom "Content1" "div" ["* > div.author + *"])
       (H.tdom "Content2" "div" ["* > div.author + *"])
       false));

    ((fmsg "inter1 </: inter2 t2"),
     (wrapper 
       (H.tdom "Author" "div" [".author"])
       (H.tdom "Author" "div" [".random"])
       false));
    
  ]

(* END subtyping_test *)
  
let test1 n =
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
  test_harness (fun _ -> test1 n) "test1 failed"

let test2 n =
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
  test_harness (fun _ -> test2 n) "test2 failed"

let test3 n =
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
  test_harness (fun _ -> test3 n) "test3 failed"

(* let test4 () = *)
(*   let test4 () = begin *)
(*     (\* *)
(*       let f = jQ<1+<'a>> -> 1<'a> in *)
(*       let g = 1<'a> in *)
(*       f g :: 1<'a> *)
(*     *\) *)
(*     (\* let p = Pos.dummy in *\) *)
(*     let open JQuery_syntax.Exp in *)
(*     let open JQuery_env in *)
(*     let txt = "type jqFirst = ['jQ<1+<'a>>] => 'jQ<1<'a>> *)
(*                type jqOneA = 'jQ<1<'a>> *)
(*                type jqZerooneB = 'jQ<01<'b>>" in *)
(*     let env = JQEnv.parse_env txt "Test env" in *)
(*     let exp = "/*:: type DOM = { name : Str }; */ *)
(*                /*:: type aDom = { name : /a/ }; */ *)
(*                /*:: type abDom = { name : /a|b/ }; */ *)
(*                var f = /*: cheat ([jQ<1+<DOM>>] => jQ<1<aDom>>) */0; *)
(*                var g = /*: cheat jQ<1<aDom>> */0; *)
(*                var ret = /*: jQ<1<abDom>>*/(f(g)); *)
(*                " in *)
(*     let js = JavaScript.parse_javascript exp "<test>" in *)
(*     let rec helper env d =  *)
(*       let open Typedjs_writtyp.WritTyp in *)
(*       match d with *)
(*       | EnvBind (_, x, _) *)
(*       | EnvType (_, x, _) *)
(*       | EnvPrim (_, x) -> IdMap.add x d env *)
(*       | RecBind ds -> List.fold_left helper env ds *)
(*       | ObjectTrio (_, (x, _), (y, _), (z, _)) -> *)
(*         IdMap.add x d (IdMap.add y d (IdMap.add x d env)) in *)
(*     let env' = List.fold_left helper IdMap.empty env in *)
(*     let new_decls = ReadTyps.new_decls (List.rev !JavaScript_lexer.comments) in *)
(*     let rec helper recIds env d =  *)
(*       let open Typedjs_writtyp.WritTyp in *)
(*       match d with *)
(*       | EnvType(p, x, t) ->  *)
(*         let t' = Desugar.desugar_typ p t in *)
(*         let t'' = squash env t' in *)
(*         (bind_rec_typ_id x recIds (TypImpl.replace_name (Some x) t'') env) *)
(*       | ObjectTrio _ -> JQEnv.extend_global_env env [d] *)
(*       | RecBind binds -> *)
(*         let ids = List.concat (List.map (fun b -> match b with *)
(*           | EnvBind (_, x, _) -> [x] *)
(*           | EnvType (_, x, _) -> [x] *)
(*           | ObjectTrio(_, (c, _), (p, _), (i, _)) -> [c;p;i] *)
(*           | EnvPrim _ *)
(*           | RecBind _ -> []) binds) in *)
(*         List.fold_left (helper ids) env binds *)
(*       | _ -> env in *)
(*     let env' = List.fold_left (helper []) env' new_decls in *)
(*     let tjs = LJSfromEJS.from_exprjs env' (Exprjs.lift_decls (Exprjs_syntax.from_javascript js)) in *)
(*     let annot =  *)
(*       let typ_db = ReadTyps.read_typs js (List.rev !JavaScript_lexer.comments) in *)
(*       WeaveAnnotations.weave typ_db tjs in *)
(*     Exp.Pretty.exp annot std_formatter; *)
(*     print_newline() *)
(*     (\*   doLet "f" (cheatTyp (TArrow(None, *\) *)
(*     (\*                               [TApp(TId("jQ"), [SMult (MOnePlus (MPlain (tDom)))])], None, *\) *)
(*     (\*                               TApp(TId("jQ"), [SMult (MOne (MPlain (TId "a")))])))) *\) *)
(*     (\*     (doLet "g" (cheatTyp (TApp(TId("jQ"), [SMult (MOne (MPlain (TId "a")))]))) *\) *)
(*     (\*        (EApp(p, EId(p, "f"), [EId (p, "g")]))) in *\) *)
(*     (\* let retTyp = (TApp(TId("jQ"), [SMult (MZeroOne (MPlain (TId "b")))])) in *\) *)
(*     (\* let env = (unchecked_bind_typ_ids [("a", TId "b")] empty_env) in *\) *)
(*     (\* begin try *\) *)
(*     (\*   text "Typechecking: Is"; newline (); *\) *)
(*     (\*   JQuery_syntax.Pretty.exp exp std_formatter; text " : "; print_typ retTyp; newline (); *\) *)
(*     (\*   text "in environment"; newline (); *\) *)
(*     (\*   braces (print_env env) std_formatter; text "?"; newline (); *\) *)
(*     (\*   with_typ_exns (fun () -> check env None exp retTyp); *\) *)
(*     (\*   text "Succeeded"; newline (); *\) *)
(*     (\* with Typ_error(p, e) -> (text "FAILED: "; text e; newline ()) end; *\) *)
(*     (\* text "Cache hits:   "; int !JQuery_subtyping.cache_hits; newline (); *\) *)
(*     (\* text "Cache misses: "; int !JQuery_subtyping.cache_misses; newline (); *\) *)
(*     (\* JQuery_subtyping.print_cache "Cache is: " std_formatter; newline() *\) *)
(*   end in *)
(*   test_harness test4 "test4 failed"*)

let test5 () = 
  let open Typedjs_writtyp.WritTyp in
  let module H = Helper in
  let helper () = 
    let text =
              "(Tweet : \"\"\"A structure for tweets\"\"\"
                   DivElement
                   optional classes = [first, last]
                   classes = [tweet]
                   /* ignore this! */
                   (Author : DivElement classes = [author] ...)
                   (Time : DivElement classes = [time] )
                    ...
                   (Content : DivElement classes = [content] ... <Tweet> ...)
                   ...
               )" in
    let decls = (JQEnv.parse_env text "dummy") in
    let env = JQEnv.extend_global_env H.env decls in
    let open Typedjs_writtyp.WritTyp in
    let print_decls () =
      List.iter (fun d -> print_env_decl d Format.std_formatter; Format.print_newline ();) decls in
    begin
      print_decls ();
      Format.print_newline ();
      print_env env;
    end in
  test_harness helper "test5 failed"

let test6 n =
  let test6 n =
    Printf.printf "All CSS succeeded: %b\n" (TestRealCSS.testSels n);
  in test_harness (fun _ -> test6 n) "test6_failed"

let test7 () =
  let helper () =
    let types = ":: type MyDOM = #{ name : Str }; 
type aDom = #{ name : /a/ }; 
type bDom = #{ name : /b/ }; 
type abDom = #{ name : /a|b/ }; 

type jQ =
  typrec jq :: M<*> => * .
    typlambda m :: M<*> .
      #{ here : 'jq<1+<'m>> };

type x = jQ<1<aDom>>;
type y = jQ<1+<abDom>>;
" in
    let decls = ReadTyps.new_decls [Pos.dummy, types] in
    let open Typedjs_writtyp.WritTyp in
    let env = IdMap.empty in
    let rec helper recIds env d = match d with
      | EnvType(p, x, t) -> 
        let t' = Desugar.desugar_typ p t in
        (* let t'' = squash env t' in *)
        (JQEnv.bind_rec_typ_id x recIds (JQuery.STyp (JQueryMod.replace_name (Some x) t')) env)
      | ObjectTrio _ -> JQEnv.extend_global_env env [d]
      | RecBind binds ->
        let ids = List.concat (List.map (fun b -> match b with
          | EnvBind (_, x, _) -> [x]
          | EnvType (_, x, _) -> [x]
          | ObjectTrio(_, (c, _), (p, _), (i, _)) -> [c;p;i]
          | Decl _
          | EnvPrim _
          | RecBind _ -> []) binds) in
        List.fold_left (helper ids) env binds
      | _ -> env in
    let env = List.fold_left (helper []) env decls in
    Printf.eprintf "%s\n" (FormatExt.to_string JQEnv.print_env env);
    Printf.eprintf "Subtyping success: %b\n" 
      (JQuerySub.subtype env (JQ.TStrobe (S.TId "x")) (JQ.TStrobe (S.TId "y")))
  in test_harness helper "test7 failed"

let well_formed_test () =
  let check_well_formed t b = match (JQ.well_formed t, b) with
    | (true, true)
    | (false, false) -> Printf.eprintf "well-form checking passed\n"
    | (true, false) -> 
      Printf.eprintf "well-form checking FAILED: ";
      (JQ.Pretty.typ t Format.std_formatter);
      Printf.eprintf "expected to be NON-well-formed\n" 
    | (false, true) -> Printf.eprintf "well-form checking FAILED: ";
      (JQ.Pretty.typ t Format.std_formatter);
      Printf.eprintf " expected to be well-formed\n" in
  let s2j s = JQ.TStrobe s in
  let j2s j = Strobe.TEmbed j in
  let top = s2j (Strobe.TTop) in
  let prim = s2j (Strobe.TPrim "jq") in
  let t1 = s2j (j2s top) in
  let t2 = s2j (j2s t1) in
  let t3 = s2j (Strobe.TUnion (None, Strobe.TTop, j2s t1)) in
  let t4 = s2j (Strobe.TThis Strobe.TTop) in
  let t5 = JQ.TApp (prim, [JQ.SMult (JQ.MSum (JQ.MOne (JQ.MPlain (s2j Strobe.TBot)), JQ.MZeroPlus (JQ.MPlain (s2j Strobe.TTop))))]) in
  let t6 = JQ.TApp (prim, [JQ.SMult (JQ.MSum (JQ.MOne (JQ.MPlain (s2j Strobe.TBot)), JQ.MZeroPlus (JQ.MPlain (s2j Strobe.TTop)))); JQ.STyp (s2j (j2s (s2j (Strobe.TId "abc"))))]) in
  let t7 = JQ.TForall (None, "test",
		       (JQ.SMult (JQ.MPlain (top))), 
		       (JQ.TLambda (None, [], 
				    s2j (Strobe.TApp 
					   (Strobe.TPrim "blah",
					    [Strobe.TId "a";
					     Strobe.TSink (None, Strobe.TBot);
					     Strobe.TThis (j2s top)]))))) in
  let t8 = s2j (Strobe.TApp (Strobe.TPrim "jq", [j2s t5])) in
  begin
    Printf.eprintf "\n";
    check_well_formed top true;
    check_well_formed prim true;
    check_well_formed t1 true;
    check_well_formed t2 true;
    check_well_formed t3 true;
    check_well_formed t4 true;
    check_well_formed t5 true;
    check_well_formed t6 true;
    check_well_formed t7 true;
    check_well_formed t8 false
  end



(* TEST: structure_well_formed_test 
   - Tests that the local structure well-formedness function is working
     properly *)
let structure_well_formed_test () = 
  let module D = Desugar in
  let module W = Typedjs_writtyp.WritTyp in

  let well_formed_wrapper d pass = 
    let decls = JQEnv.parse_env d 
      "Simple_tests: Structure well-formedness test" in

    let structure_decls = ListExt.filter_map (fun d -> match d with
      | W.Decl (_, dc) -> Some dc | _ -> None) decls in

    try
      ignore(D.well_formed_structure structure_decls);
      if (not pass) then raise (STest_failure "Well-formed test should have raised an exception")
    with e -> 
      match e with 
      | D.Local_structure_error m -> if (not pass) then () else raise e
      | _ -> raise e in

  let fail_msg desc n =
    "Structure_well_formed_test #" ^ (string_of_int (n+1)) ^ " failed.\n" ^
    "Description: " ^ desc in

  (* well-formedness tests *)

  test_harness_many [ 

    (**** Rule 1: Cannot have more than one comp with the same id in
          the entire env. *)
    
    ((fail_msg "Dupes in two top-level comps"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1])
       (A : div classes=[a2])" false ));
    
    ((fail_msg "Nested dupes in same top-level comp"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (B : div classes=[b1])
           (C : div classes=[c1]
             (B : div classes=[b2])))" false));

    ((fail_msg "Dupes on the same level in the same top-level comp"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (B : div classes=[b1])
         (B : div classes=[b2]))" false ));


    ((fail_msg "Dupes in different levels and different top-level comps"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (C : div classes=[c1]
           (B : div classes=[b1])))
       (D : div classes=[d1]
         (E : div classes=[e1]
           (F : div classes=[f1]
             (B : div classes=[b2]))))" false ));

    ((fail_msg "Can have multiple dupe ids so long as there is only one comp"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (C : div classes=[c1])
         (B : div classes=[b1])
         <B>
         (D : div classes=[d1])
         <B>)" true ));

    
    (**** Rule 2 DIds can only appear on the same level as a previous sibling
        DNested declComp with the same id *)

    ((fail_msg "DId cannot appear before comp"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         <B>
         (C : div classes=[c1])
         (B : div classes=[b1]))" false ));

    ((fail_msg "DId can appear after comp"),
     (fun _ -> well_formed_wrapper
       "(A : div classes=[a1]
         (B : div classes=[b1])
         (C : div classes=[c1])
         <B>)" true ));

    ((fail_msg ("Can have as many DIds as wanted on the same level so" ^
        "long as they appear after their respective comp")),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (B : div classes=[b1])
         <B>
         (C : div classes=[b1])
         <B>
         <B>
         <B>)" true ));

    ((fail_msg "Can't be used above"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (C : div classes=[c1]
           (B : div classes=[b1]))
         <B>)" false ));

    ((fail_msg "Can be used below"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (B : div classes=[b1])
         (C : div classes=[c1])
         (D : div classes=[d1])
         <B>)" true));

    ((fail_msg "Crossover nested in a top-level comp"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (C : div classes=[c1]
           <B>))
       (D : div classes=[d1]
         (B : div classes=[b2]))" false));

    ((fail_msg "Crossover with a top-level comp"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         <B>)
       (B : div classes=[b1])" false ));

    
    (**** Rule 4: Cannot have two consectutive placeholders *)
    
    ((fail_msg "Can't have only two placeholders as children"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         ...
         ...)" false));


    ((fail_msg "Can't have only adjacent placeholders at beginning"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         ...
         ...
         (B: div classes=[b1])
         (C: div classes=[c1]))" false));


    ((fail_msg "Can't have two adjacent placeholders in middle"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (B: div classes=[b1])
         ...
         ...
         (C: div classes=[c1]))" false));

    ((fail_msg "Can't have two adjacent placeholders at end"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         (B: div classes=[b1])
         (C: div classes=[c1])
         ...
         ...)" false));

    ((fail_msg "Can have alternating placeholders"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         ...
         (B: div classes=[b1])
         ...
         (C: div classes=[c1])
         ...)" true));


    ((fail_msg "Can have single placeholder child"),
    (fun _ -> well_formed_wrapper
      "(A : div classes=[a1]
         ...)" true));


  ] (* End list of tests *)

(* End structure_well_formed_test *)


let structure_compilation_test () = 
  let module D = Desugar in
  let module W = Typedjs_writtyp.WritTyp in
  let module Css = JQueryMod.Css in
  let open S in
  let open JQ in
  let module H = Helper in

  (* Consumes:
     d (string): structure declarations to be parsed
     exp_backform_env (D.backformEnv): expected backformEnv
     exp_clause_env (D.clauseEnv): expected clauseEnv *)
  let wrapper d (exp_backform_env : D.backformEnv) (exp_clause_env : D.clauseEnv)
      : unit  = 

    let decls = JQEnv.parse_env d "Simple_tests: Structure Compilation Test" in



    (* IMPORTANT: This is an uncomfortable dependency; in order to compute the
       env, we must use desugar_structure, which is what we're testing
       here. We need the env, however, to test equivalent multiplicities.
       equivalent_multiplicity is not enough - we need to check for invariant 
       subtyping. But to do that we need the env.

       I believe what we're doing is ok, however. The reason for this is that
       the parts of the env that are RELEVANT to subtype_multiplicity are
       the results of gen_bindings in desugar structure, and H.env. So,
       computation of the env does NOT depend on the clauseMaps. It seems,
       therefore, that this is ok because it is a a ONE-WAY dependency. *)

    let env = JQEnv.extend_global_env H.env decls in

    let structure_decls = ListExt.filter_map (fun d -> match d with
      | W.Decl (_, dc) -> Some dc | _ -> None) decls in

    let expected_senv = (exp_backform_env, exp_clause_env) in

    let (_, senv) = D.desugar_structure structure_decls in
    let (backform_env, clause_env) = senv in

    (* Note this does not check to make sure that the SelSets have
       the SAME selectors, just that they are equivalent. This has
       the unfortunate side-effect of making it too easy for some 
       tests to pass *)
    let beq = D.benv_eq exp_backform_env backform_env in

    let ceq = 
      let cm_eq m1 m2 = IdMap.equal (fun m1 m2 ->
      JQuerySub.subtype_mult true env m1 m2 &&
        JQuerySub.subtype_mult true env m2 m1) m1 m2 in
      cm_eq clause_env.D.children exp_clause_env.D.children &&      
        cm_eq clause_env.D.parent exp_clause_env.D.parent &&      
        cm_eq clause_env.D.prev exp_clause_env.D.prev &&      
        cm_eq clause_env.D.next exp_clause_env.D.next in  

    begin 

      if beq then ()
      else raise 
        (STest_failure 
           (sprintf "Expected backformEnv in structureEnv: %s  is not equivalent to compiled backformEnv in structureEnv: %s" 
              (FormatExt.to_string (JQEnv.print_structureEnv "Expected") expected_senv)
              (FormatExt.to_string (JQEnv.print_structureEnv "Compiled") senv)));
        
      if ceq then ()
      else raise
        (STest_failure 
           (sprintf "Expected clauseEnv in structureEnv: %s  is not equivalent to compiled clauseEnv in structureEnv: %s" 
              (FormatExt.to_string (JQEnv.print_structureEnv "Expected") expected_senv)
              (FormatExt.to_string (JQEnv.print_structureEnv "Compiled") senv)));
      


    end in

  (* Helper: builds an MPlain from a list of ids. *)
  let b_mp (ts : string list) : JQ.multiplicity = match ts with
    | [] -> failwith "Can't build type with no ids"
    | _ -> 
      let catch_tany t = if t = "Bot" then TBot else TId t in
      let built_typ = List.fold_left (fun acc t -> 
        (* Fix so that we can represent Any in string form *)
        TUnion (None, catch_tany t, acc))
        (catch_tany (List.hd ts)) (List.tl ts) in
      MPlain (TStrobe built_typ) in

  (* Helper: builds a clauseMap from a (id * multiplicity) list.
     Adds to the original clauseMap, cm *)
  let b_cm cm (cs : (id * multiplicity) list ) : D.clauseMap =
    List.fold_left (fun acc (id, mult) -> 
      IdMap.add id mult acc) cm cs in
  
  (* base clauseMap with Element clauses *)
  let base_clauseMap =
    { D.children = b_cm IdMap.empty [("Element", MZeroPlus (b_mp ["Element"]))];
      D.parent = b_cm IdMap.empty [("Element", MZeroOne (b_mp ["Element"]))];
      D.prev = b_cm IdMap.empty [("Element", MZeroOne (b_mp ["Element"]))];
      D.next = b_cm IdMap.empty [("Element", MZeroOne (b_mp ["Element"]))] } in


  (* Helper: builds an MSum from a list of multiplicities *)
  let b_msum (ms : multiplicity list) : multiplicity = match ms with
    | [] -> failwith "Simple_tests: structure_compilation_test: Need at least two multiplicites to build an MSum, fool!"
    | [m] -> failwith "Simple_tests: structure_compilation_test: Need at least two multiplicities to build an MSum, fool!"
    | hd::tl -> List.fold_left (fun acc m -> MSum (m,acc)) hd tl in


  (* Helper: builds a clauseMap by extending the base clauseMap *)
  let ch cs = b_cm base_clauseMap.D.children cs in
  let par cs = b_cm base_clauseMap.D.parent cs in
  let prev cs = b_cm base_clauseMap.D.prev cs in
  let next cs = b_cm base_clauseMap.D.next cs in


  let fmsg d n = "Structure compilation test #" ^ (string_of_int n) ^
    "failed. Test description: " ^ d ^ "\n" in

  test_harness_many [

    (*** Begin compilation tests ***)

    ((fmsg "Single top-level declComp"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1])"
       ["Tweet", H.sel ["div.!t1"]]
       { D.children = ch [("Tweet", MZero (b_mp ["Bot"]))];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]))];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]))];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]))] }));


    ((fmsg "Single author as a child"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1]
          (Author : div classes=[a1]))"
       [("Tweet", H.sel ["div.!t1"]);
        ("Author", H.sel ["div.!t1 > div.!a1"]);]
       { D.children = ch [("Tweet", MOne (b_mp ["Author"]));
                          ("Author", MZero (b_mp ["Bot"]))];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]));
                         ("Author", MOne (b_mp ["Tweet"]))];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZero (b_mp ["Bot"]))];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZero (b_mp ["Bot"]))]; }));

    ((fmsg "Multiple top-level declComps"),
     (fun _ -> wrapper
       "(A : div classes=[a1])
        (B : div classes=[b1])"
       [("A", H.sel ["div.!a1"]);
        ("B", H.sel ["div.!b1"])]
       { D.children = ch [("A", MZero (b_mp ["Bot"]));
                          ("B", MZero (b_mp ["Bot"]))];
         D.parent = par [("A", MZeroOne (b_mp ["Element"]));
                         ("B", MZeroOne (b_mp ["Element"]))];
         D.prev = prev [("A", MZeroOne (b_mp ["Element"]));
                        ("B", MZeroOne (b_mp ["Element"]))];
         D.next = next [("A", MZeroOne (b_mp ["Element"]));
                        ("B", MZeroOne (b_mp ["Element"]))] }));


    ((fmsg "Multiple top-level declComps with many nested children"),
     (fun _ -> wrapper
       "(A : div classes=[a1]
           (B : div classes=[b1]
              (C : div classes=[c1])))
        (D : div classes=[d1]
           (E : div classes=[e1]
              (F : div classes=[f1])))"
       [("A", H.sel ["div.!a1"]);
        ("B", H.sel ["div.!a1 > div.!b1"]);
        ("C", H.sel ["div.!a1 > div.!b1 > div.!c1"]);
        ("D", H.sel ["div.!d1"]);
        ("E", H.sel ["div.!d1 > div.!e1"]);
        ("F", H.sel ["div.!d1 > div.!e1 > div.!f1"])]
       { D.children = ch [("A", MOne (b_mp ["B"]));
                          ("B", MOne (b_mp ["C"]));
                          ("C", MZero (b_mp ["Bot"]));
                          ("D", MOne (b_mp ["E"]));
                          ("E", MOne (b_mp ["F"]));
                          ("F", MZero (b_mp ["Bot"]))];
         D.parent = par  [("A", MZeroOne (b_mp ["Element"]));
                          ("B", MOne (b_mp ["A"]));
                          ("C", MOne (b_mp ["B"]));
                          ("D", MZeroOne (b_mp ["Element"]));
                          ("E", MOne (b_mp ["D"]));
                          ("F", MOne (b_mp ["E"]))];
         D.prev = prev  [("A", MZeroOne (b_mp ["Element"]));
                         ("B", MZero (b_mp ["Bot"]));
                         ("C", MZero (b_mp ["Bot"]));
                         ("D", MZeroOne (b_mp ["Element"]));
                         ("E", MZero (b_mp ["Bot"]));
                         ("F", MZero (b_mp ["Bot"]))];
         D.next = next  [("A", MZeroOne (b_mp ["Element"]));
                         ("B", MZero (b_mp ["Bot"]));
                         ("C", MZero (b_mp ["Bot"]));
                         ("D", MZeroOne (b_mp ["Element"]));
                         ("E", MZero (b_mp ["Bot"]));
                         ("F", MZero (b_mp ["Bot"]))]; }));


    ((fmsg "Multiple children with the same name"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1]
          (Author : div classes=[a1])
          <Author>
          <Author>)"
       [("Tweet", H.sel ["div.!t1"]);
        ("Author", H.sel ["div.!t1 > div.!a1"])]
       { D.children = ch [("Tweet", MOnePlus (b_mp ["Author"]));
                          ("Author", MZero (b_mp ["Bot"]))];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]));
                         ("Author", MOne (b_mp ["Tweet"]))];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZeroOne (b_mp ["Author"]))];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZeroOne (b_mp ["Author"]))]; }));

    ((fmsg "Multiple children with same name interspersed with placeholders"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1]
          ...
          (Author : div classes=[a1])
          ...
          <Author>
          <Author>
          ...
          <Author>)"
       [("Tweet", H.sel ["div.!t1"]);
        ("Author", H.sel ["div.!t1 > div.!a1"])]
       { D.children = ch [("Tweet", b_msum [MOnePlus (b_mp ["Author"]);
                                            MZeroPlus (b_mp ["Element"])]);
                          ("Author", MZero (b_mp ["Bot"]))];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]));
                         ("Author", MOne (b_mp ["Tweet"]))];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MOne (b_mp ["Author"; "Element"]))];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZeroOne (b_mp ["Author"; "Element"]))]; }));


    ((fmsg "Multiple children with several same-name DIds interspersed with placeholders"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1]
          ...
          (Author : div classes=[a1])
          ...
          <Author>
          (Content : div classes=[c1])
          <Author>
          <Content>
          ...
          <Author>)"
       [("Tweet", H.sel ["div.!t1"]);
        ("Author", 
         H.sel ["div.!t1 > div.!a1";
              "div.!t1 > div.!a1 ~ div.!a1";
              "div.!t1 > div.!a1 ~ div.!a1 + div.!c1 + div.!a1";
              "div.!t1 > div.!a1 ~ div.!a1 + div.!c1 + div.!a1 + div.!c1 ~ div.!a1"]);
        ("Content", 
         H.sel ["div.!t1 > div.!a1 ~ div.!a1 + div.!c1";
              "div.!t1 > div.!a1 ~ div.!a1 + div.!c1 + div.!a1 + div.!c1"])]
       { D.children = ch [("Tweet", 
                           b_msum [
                             MOnePlus (b_mp ["Author"]);
                             MZeroPlus (b_mp ["Element"]);
                             MOnePlus (b_mp ["Content"];)]);
                           ("Author", MZero (b_mp ["Bot"]));
                           ("Content", MZero (b_mp ["Bot"]))];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]));
                         ("Author", MOne (b_mp ["Tweet"]));
                         ("Content", MOne (b_mp ["Tweet"]))];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MOne (b_mp ["Author";"Element";"Content"]));
                        ("Content", MOne (b_mp ["Author"]))];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZeroOne (b_mp ["Author"; "Element"; "Content"]));
                        ("Content", MOne (b_mp ["Author"; "Element"]))]; }));



    ((fmsg "Single placeholder as a child"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1]
          ...)"
       [("Tweet", H.sel ["div.!t1"]);]
       { D.children = ch [("Tweet", MZeroPlus (b_mp ["Element"]));];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]));];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]));];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]));]; }));


    ((fmsg "Single placeholder following one named child"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1]
          (Author : div classes=[a1])
          ...)"
       [("Tweet", H.sel ["div.!t1"]);
       ("Author", H.sel ["div.!t1 > div.!a1"])]
       { D.children = ch [("Tweet", b_msum [MOne (b_mp ["Author"]);
                                            MZeroPlus (b_mp ["Element"])]);
                          ("Author", MZero (b_mp ["Bot"]))];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]));
                         ("Author", MOne (b_mp ["Tweet"]))];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZero (b_mp ["Bot"]))];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZeroOne (b_mp ["Element"]))]; }));

    ((fmsg "Single placeholder preceding one named child"),
     (fun _ -> wrapper
       "(Tweet : div classes=[t1]
          ...
          (Author : div classes=[a1]))"
       [("Tweet", H.sel ["div.!t1"]);
       ("Author", H.sel ["div.!t1 > div.!a1"])]
       { D.children = ch [("Tweet", b_msum [MOne (b_mp ["Author"]);
                                            MZeroPlus (b_mp ["Element"])]);
                          ("Author", MZero (b_mp ["Bot"]))];
         D.parent = par [("Tweet", MZeroOne (b_mp ["Element"]));
                         ("Author", MOne (b_mp ["Tweet"]))];
         D.prev = prev [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZeroOne (b_mp ["Element"]))];
         D.next = next [("Tweet", MZeroOne (b_mp ["Element"]));
                        ("Author", MZero (b_mp ["Bot"]))]; }));


    
    ((fmsg "Terribad comprehensive test case"),
     (fun _ -> wrapper
       "(Tweet : div classes=[tweet] optional classes=[first,last]
          ...
          (Author : div classes=[author] optional classes=[featured]
             (Bio : div classes=[bio] optional classes=[hidden]
                ...)
             ...)
          (Content : div classes=[content])
          ...
          (Image : div classes=[image])
          <Image>
          (Time : div classes=[time]))"
       [("Tweet", H.sel ["div.!tweet.?first.?last"]);
        ("Author", H.sel ["div.!tweet.?first.?last > div.!author.?featured"]);
        ("Bio", H.sel ["div.!tweet.?first.?last > div.!author.?featured > div.!bio.?hidden"]);
        ("Content", H.sel ["div.!tweet.?first.?last > div.!author.?featured + div.!content"]);
        ("Image", H.sel ["div.!tweet.?first.?last > div.!author.?featured + div.!content ~ div.!image";
                       "div.!tweet.?first.?last > div.!author.?featured + div.!content ~ div.!image + div.!image"]);
        ("Time", H.sel ["div.!tweet.?first.?last > div.!author.?featured + div.!content ~ div.!image + div.!image + div.!time"]);]
       { D.children = ch
           [("Tweet", b_msum [MOne (b_mp ["Author"]);
                              MOne (b_mp ["Content"]);
                              MOne (b_mp ["Time"]);
                              MOnePlus (b_mp ["Image"]);
                              MZeroPlus (b_mp ["Element"]);]);
            ("Author", b_msum [MOne (b_mp ["Bio"]);
                               MZeroPlus (b_mp ["Element"])]);
            ("Bio", MZeroPlus (b_mp ["Element"]));
            ("Content", MZero (b_mp ["Bot"]));
            ("Image", MZero (b_mp ["Bot"]));
            ("Time", MZero (b_mp ["Bot"]));];
         D.parent = par 
           [("Tweet", MZeroOne (b_mp ["Element"]));
            ("Author", MOne (b_mp ["Tweet"]));
            ("Bio", MOne (b_mp ["Author"]));
            ("Content", MOne (b_mp ["Tweet"]));
            ("Image", MOne (b_mp ["Tweet"]));
            ("Time", MOne (b_mp ["Tweet"]));];
         D.prev = prev 
           [("Tweet", MZeroOne (b_mp ["Element"]));
            ("Author", MZeroOne (b_mp ["Element"]));
            ("Bio", MZero (b_mp ["Bot"]));
            ("Content", MOne (b_mp ["Author"]));
            ("Image", MOne (b_mp ["Element";"Content";"Image";]));
            ("Time", MOne (b_mp ["Image"]));];
         D.next = next 
           [("Tweet", MZeroOne (b_mp ["Element"]));
            ("Author", MOne (b_mp ["Content"]));
            ("Bio", MZeroOne (b_mp ["Element"]));
            ("Content", MOne (b_mp ["Element";"Image"]));
            ("Image", MOne (b_mp ["Image"; "Time"]));
            ("Time", MZero (b_mp ["Bot"]));]; }));

  ]
(* end structure_compilation_test *)


let selector_tests () =
  match List.map Css.singleton 
  ["div.author.tag";
   "div.!tweet.?first.?last > div.!author.!tag + div.!time";
   "div.!tweet.?first.?last > div.!author.!tag + div.!time + div.!content.!tag";
   "div.!tweet.?first.?last";
   "div.!tweet.?first.?last > div.!author.!tag";
   "div.!tweet>div.!author";
   "div.!tweet>div.!author+div.!author"] with
  | s1::time::content::tweet::author::a1::a2::_ -> begin
    let subset_wrapper s1 s2 b =
      if b = (Css.is_subset IdMap.empty s1 s2) then () else begin
        Printf.eprintf "trying to subset %s with %s, expected to be %b" (Css.pretty s1) (Css.pretty s2) b;
        raise (STest_failure "subset test did not pass")
      end
    in

    let fail_msg s1 s2 n =
      "Selector_test #" ^ (string_of_int (n+1)) ^ " failed.\n" ^
        (Css.pretty s1) ^ " <?: " ^ (Css.pretty s2) in


    test_harness_many [
      ((fail_msg s1 time),
       (fun _ -> subset_wrapper s1 time false));

      ((fail_msg s1 author),
       (fun _ -> subset_wrapper s1 author false));
     
      ((fail_msg a1 a2),
       (fun _ -> subset_wrapper a1 a2 false));
      
    ]
  end
  | _ -> []


let run_tests () =
  try
    (* Random.self_init(); *)
    (* test1 500; *)
    (* test2 500; *)
    (* test3 100; *)
    (* (\* test4 (); *\) *)
    (* test5 (); *)
    (* test6 1000; *)
    (* test7 (); *)
    (* well_formed_test (); *)
    (raise_exns [
      expose_tdoms_test;
      subtyping_test;
      structure_well_formed_test;
      structure_compilation_test;
      selector_tests;
    ]);
    (* test5 (); *)
    Printf.eprintf "All tests passed!";
    0
  with e -> 
    Printf.eprintf "Failed with %s" (Printexc.to_string e);
    2
;;

