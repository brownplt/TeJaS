open Prelude
open Sig
open Main_actions
open JQuery_syntax
open Format
open FormatExt
module SimpleTests = Simple_tests

module JQ = JQueryImpl
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

module WeaveAnnotations = WeaveAnnotations.Make (Exp) (Desugar)
module LJSfromEJS = Typedjs_fromExpr.Make (Exp)

module Actions : MAIN_ACTIONS = struct

  let src_js : JavaScript_syntax.prog option ref = ref None
  let src_ljs : Exprjs_syntax.expr option ref = ref None
  let init_with_asts (js, ljs) =
    src_js := Some js;
    src_ljs := Some ljs

  let env : JQEnv.env ref = ref IdMap.empty
  let global_object = ref None

  let load_env (fname : string) : unit =
    env := JQEnv.extend_global_env !env (JQEnv.parse_env_file (open_in fname) fname)

  let set_env new_env = env := new_env
  let set_global_object cname = match !global_object with
    | None -> global_object := Some cname
    | Some _ -> failwith "jst: global object already specified"

  let get_env () = !env
  let get_global_object () = match !global_object with
    | None -> "Global"
    | Some c -> c

  let get_typedjs () =
    match !src_ljs with
      | Some ejs -> LJSfromEJS.from_exprjs (get_env ()) ejs
      | None -> failwith "jQuery: Fatal, didn't get ljs from main"


  let default_typ : JQ.typ option ref = ref None

  let assert_typ : JQ.typ option ref = ref None

  let weave_annotations typedjs =
    match !src_js with
      | None -> typedjs
      | Some js ->
        let typ_db = ReadTyps.read_typs js (List.rev !JavaScript_lexer.comments) in
        WeaveAnnotations.weave typ_db typedjs

  let weave_assertions typedjs =
    match !assert_typ with
    | None -> typedjs
    | Some typ -> WeaveAnnotations.assert_typ typ typedjs

  let rec elim_twith env exp = 
    let open Exp in
    let elim = elim_twith env in match exp with
    | EAssertTyp(p, t, e) -> EAssertTyp(p, JQuery.squash env t, elim e)
    | EArray(p, es) -> EArray(p, map elim es)
    | EObject (p, props) -> EObject (p, map (second2 elim) props)
    | EId _ -> exp
    | EBracket (p, e1, e2) -> EBracket (p, elim e1, elim e2)
    | EUpdate (p, e1, e2, e3) -> EUpdate (p, elim e1, elim e2, elim e3)
    | EPrefixOp (p, op, e) -> EPrefixOp (p, op, elim e)
    | EInfixOp (p, op, e1, e2) -> EInfixOp (p, op, elim e1, elim e2)
    | EIf (p, e1, e2, e3) -> EIf (p, elim e1, elim e2, elim e3)
    | EApp (p, e, es) -> EApp (p, elim e, map elim es)
    | EFunc (p, xs, info, e) -> EFunc (p, xs, info, elim e)
    | ELet (p, x, e1, e2) -> 
      let e1' = elim e1 in
      let e2' = elim e2 in
      ELet (p, x, e1', e2')
    | ERec (p, binds, e) -> ERec (p, map (third3 elim) binds, elim e)
    | ESeq (p, e1, e2) -> ESeq (p, elim e1, elim e2)
    | ELabel (p, x, e) -> ELabel (p, x, elim e)
    | EBreak (p, x, e) -> EBreak (p, x, elim e)
    | ETryCatch (p, e1, x, e2) -> ETryCatch (p, elim e1, x, elim e2)
    | ETryFinally (p, e1, e2) -> ETryFinally (p, elim e1, elim e2)
    | EThrow (p, e) -> EThrow (p, elim e)
    | ETypecast (p, rt, e) -> ETypecast (p, rt, elim e)
    | ERef (p, k, e) -> ERef (p, k, elim e)
    | EDeref (p, e) -> EDeref (p, elim e)
    | ESetRef (p, e1, e2) -> ESetRef (p, elim e1, elim e2)
    | EParen (p, e) -> EParen (p, elim e)
    | ESubsumption (p, t, e) -> ESubsumption (p, JQuery.squash env t, elim e)
    | EDowncast (p, t, e) -> EDowncast (p, JQuery.squash env t, elim e)
    | ETypAbs (p, x, t, e) -> ETypAbs (p, x, JQuery.squash env t, elim e)
    | ETypApp (p, e, t) -> ETypApp (p, elim e, JQuery.squash env t)
    | ECheat (p, t, e) -> ECheat (p, JQuery.squash env t, elim e)
    | EBot _
    | EConst _ -> exp

  let do_print_env = ref false

  let print_env env : unit =
    JQEnv.print_env env std_formatter;
    JQEnv.print_structureEnv "Structure environment is: " !JQEnv.senv std_formatter;
    Format.print_newline ()

  let set_print_env () : unit =
   do_print_env := true

  let actual_data () =
    let open Typedjs_writtyp.WritTyp in
    let env =
      JQEnv.set_global_object (get_env ()) (get_global_object ()) in
      (* let typ_vars = Unidl.unidl !idl_defs in *)
      (* Typedjs_env.set_global_object *)
      (*   (extend_env IdMap.empty typ_vars (get_env ())) *)
      (*   (get_global_object ()) in *)
    let typedjs = get_typedjs () in
    let new_decls = ReadTyps.new_decls (List.rev !JavaScript_lexer.comments) in
    let env = JQEnv.extend_global_env env new_decls in
    set_env env;
    let annot_js = elim_twith env (weave_annotations typedjs) in
    let asserted_js = weave_assertions annot_js in
    (env, asserted_js)


  let action_pretypecheck () : int =
    let (env, typedjs) = actual_data () in
    if (!do_print_env) then print_env env;
    Exp.Pretty.exp typedjs std_formatter;
    0

  let do_show_cache = ref false

  let show_cache () = do_show_cache := true

  let action_tc () : int = timefn "Typechecking" (fun () ->
    let (env, asserted_js) = actual_data () in
    if (!do_print_env) then print_env env;
    JQueryTC.typecheck env !default_typ asserted_js;
    if !do_show_cache then begin
      Pervasives.flush stdout;
      Pervasives.flush stderr;
      Printf.printf "Cache hits:   %d, %d\n" (JQuerySub.num_cache_hits ()) (StrobeSub.num_cache_hits ());
      Printf.printf "Cache misses: %d, %d\n" (JQuerySub.num_cache_misses ()) (StrobeSub.num_cache_misses ());
      JQuerySub.print_cache "JQuery Cache is: " Format.std_formatter; Format.print_newline();
      StrobeSub.print_cache "Strobe Cache is: " Format.std_formatter; Format.print_newline()
    end;
    if Strobe.get_num_typ_errors () > 0 then begin
      Printf.eprintf "Typechecking failed\n";
      2
    end else begin
      Printf.eprintf "Typechecking succeeded\n";
      0
    end
  ) ()

  let parseTyp_to_ref typStr typref =
    let open Lexing in
    let start_pos = { pos_fname = "<string>"; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 } in
    let len = String.length typStr in
    let end_pos = { pos_fname = "<string>"; pos_lnum = 1; pos_bol = len; pos_cnum = len } in
    let pos = Pos.real (start_pos, end_pos) in
    match LJSfromEJS.parse_annotation pos typStr with
    | Typedjs_writtyp.WritTyp.ATyp typ ->
      let typ = Desugar.desugar_typ pos typ in
      typref := Some typ
    | _ -> ()

  let allow_unbound typStr : unit =
    parseTyp_to_ref typStr default_typ

  let assert_typ typStr : unit = 
    parseTyp_to_ref typStr assert_typ

  let provided_actions set_action = [
      ("-tc", Arg.Unit (set_action action_tc),
       "type-check the source program (default when no options are given)");
      ("-print-cache", Arg.Unit show_cache,
       "Print cache results after typechecking");
      ("-env", Arg.String (fun s -> load_env s),
       "<file> read environment types from <file>");
      ("-global", Arg.String (fun s -> set_global_object s),
       "<class> use <class> as the global object");
      ("-pretc", Arg.Unit (set_action action_pretypecheck),
       "basic well-formedness checks before type-checking and flow-analysis");
      ("-allow-unbound", Arg.String allow_unbound,
       "Permit unbound global variables, with default type given by the argument");
      ("-verbose-errors", Arg.Unit (fun () -> JQueryMod.Pretty.useNames false),
       "Print types structurally, rather than with pretty names");
      ("-assert-typ", Arg.String assert_typ,
       "Assert that all un-annotated assignments have a given type");
      ("-print-typ", Arg.String (fun ty ->
        let (typ, _) = JQEnv.lookup_typ_id ty (get_env ()) in
        horz [text ty; text "="; JQueryMod.Pretty.typ (JQueryMod.replace_name None typ)] std_formatter;
        Format.pp_print_flush std_formatter ()),
       "Print the definition of a single type");
      ("-print-env", Arg.Unit set_print_env,
       "Print the current environment");
      ("-simple-tests", Arg.Unit (set_action SimpleTests.run_tests),
       "Run a suite of simple tests")
(*      ("-strict-selections", Arg.Unit (JQEnv.do_use_strict_selections),
       "When making a selection that is not isolated, return 0<Element>") *)
       ]
end
