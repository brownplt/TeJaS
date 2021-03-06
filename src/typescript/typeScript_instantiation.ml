open Prelude
open Format
open FormatExt
open TypeScript_syntax
open Main_actions

module B = TypeScriptImpl
module S = StrobeImpl
module Desugar = TypeScript_desugar.Make (StrobeMod) (TypeScriptMod)
module SEnv = Strobe_env.Make (StrobeMod) (Strobe_kind) (Desugar)
module TypeScriptEnv = TypeScript_env.MakeExt (TypeScriptMod) (TypeScript_kind) (SEnv) (Desugar)

module rec TypeScriptSub : (TypeScript_sigs.TYPESCRIPT_SUBTYPING
                        with type typ = TypeScriptImpl.typ
  with type kind = TypeScriptImpl.kind
  with type binding = TypeScriptImpl.binding
  with type env = TypeScriptImpl.env
  with type baseTyp = TypeScriptImpl.baseTyp
  with type baseKind = TypeScriptImpl.baseKind
  with type baseBinding = TypeScriptImpl.baseBinding) =
  TypeScript_subtyping.MakeActions (StrobeSub) (TypeScriptMod) (TypeScriptEnv)
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
  Strobe_subtyping.MakeActions (StrobeMod) (TypeScriptSub) (TypeScriptEnv)


module DummySemicfa = struct
  type env = TypeScriptEnv.env
  type exp = Exp.exp
  let semicfa _ _ e = e
end
module DummyStatic = struct
  type typ = TypeScriptEnv.typ
  type env = TypeScriptEnv.env
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
  Strobe_typechecking.Make (StrobeMod) (Exp) (TypeScriptEnv) (StrobeSub) (TypeScript_kind) (DummySemicfa) (DummyStatic) (TypeScriptTC)
and TypeScriptTC : (TypeScript_sigs.TYPESCRIPT_TYPECHECKING
                       with type typ = TypeScriptImpl.typ
  with type kind = TypeScriptImpl.kind
  with type binding = TypeScriptImpl.binding
  with type env = TypeScriptImpl.env
  with type baseTyp = TypeScriptImpl.baseTyp
  with type baseKind = TypeScriptImpl.baseKind
  with type baseBinding = TypeScriptImpl.baseBinding
  with type exp = Exp.exp) =
  TypeScript_typechecking.Make (TypeScriptMod) (Exp) (TypeScriptEnv) (TypeScriptSub) (TypeScript_kind) (StrobeTC)

module WeaveAnnotations = TypeScript_weaveAnnotations.Make (Exp) (Desugar)
module LJSfromEJS = Typedjs_fromExpr.Make (Exp)

module Actions : MAIN_ACTIONS = struct

  let src_js : JavaScript_syntax.prog option ref = ref None
  let src_ljs : Exprjs_syntax.expr option ref = ref None
  let init_with_asts (js, ljs) =
    src_js := Some js;
    src_ljs := Some ljs

  let env : TypeScriptEnv.env ref = ref IdMap.empty
  let global_object = ref None

  let load_env (fname : string) : unit =
    env := TypeScriptEnv.extend_global_env !env (TypeScriptEnv.parse_env_file (open_in fname) fname)

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

  let weave_annotations typedjs =
    match !src_js with
      | None -> typedjs
      | Some js ->
        let typ_db = ReadTyps.read_typs js (List.rev !JavaScript_lexer.comments) in
        WeaveAnnotations.weave typ_db typedjs

  let rec expose_twith env exp =
    let open Exp in
    let elim = expose_twith env in match exp with
    | EAssertTyp(p, t, e) -> EAssertTyp(p, TypeScript.expose_twith env t, elim e)
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
    | ESubsumption (p, t, e) -> ESubsumption (p, TypeScript.expose_twith env t, elim e)
    | EDowncast (p, t, e) -> EDowncast (p, TypeScript.expose_twith env t, elim e)
    | ETypAbs (p, x, t, e) -> ETypAbs (p, x, TypeScript.expose_twith env t, elim e)
    | ETypApp (p, e, t) -> ETypApp (p, elim e, TypeScript.expose_twith env t)
    | ECheat (p, t, e) -> ECheat (p, TypeScript.expose_twith env t, elim e)
    | EBot _
    | EConst _ -> exp

  let extract_new_decls () =
    let open Typedjs_writtyp.WritTyp in
    let env =
      TypeScriptEnv.set_global_object (get_env ()) (get_global_object ()) in
      (* let typ_vars = Unidl.unidl !idl_defs in *)
      (* Typedjs_env.set_global_object *)
      (*   (extend_env IdMap.empty typ_vars (get_env ())) *)
      (*   (get_global_object ()) in *)
    let new_decls = ReadTyps.new_decls (List.rev !JavaScript_lexer.comments) in
    let env = TypeScriptEnv.extend_global_env env new_decls in
    set_env env

  let actual_data () =
    extract_new_decls ();
    let typedjs = get_typedjs () in
    let env = get_env () in
    let annot_js = expose_twith env (weave_annotations typedjs) in
    (env, annot_js)

  let default_typ : B.typ option ref = ref None

  let action_tc () : int = timefn "Typechecking" (fun () ->
    let (env, asserted_js) = actual_data () in
    TypeScriptTC.typecheck env !default_typ asserted_js;
    if Strobe.get_num_typ_errors () > 0 then begin
      Printf.eprintf "Typechecking failed\n";
      2
    end else begin
      Printf.eprintf "Typechecking succeeded\n";
      0
    end
  ) ()

  let action_pretypecheck () : int =
    let (env, typedjs) = actual_data () in
(*    if (!do_print_env) then print_env env; *)
    Exp.Pretty.exp typedjs std_formatter;
    0

  let print_env () : int =
    extract_new_decls ();
    TypeScriptEnv.print_env (get_env ()) std_formatter;
    Format.pp_print_flush std_formatter ();
    0

  let provided_actions set_action = [
      ("-env", Arg.String (fun s -> load_env s),
       "<file> read environment types from <file>");
      ("-tc", Arg.Unit (set_action action_tc),
       "type-check the source program (default when no options are given)");
      ("-pretc", Arg.Unit (set_action action_pretypecheck),
       "basic well-formedness checks before type-checking and flow-analysis");
      ("-print-typ", Arg.String (fun ty -> set_action (fun () ->
        extract_new_decls ();
        let (typ, _) = TypeScriptEnv.lookup_typ_id ty (get_env ()) in
        horz [text ty; text "="; TypeScriptMod.Pretty.typ (TypeScriptMod.replace_name None typ)] std_formatter;
        Format.pp_print_flush std_formatter (); 0) ()),
       "Print the definition of a single type");
      ("-verbose-errors", Arg.Unit (fun () -> TypeScriptMod.Pretty.useNames false),
       "Print types structurally, rather than with pretty names");
      ("-print-env", Arg.Unit (set_action print_env),
       "Print the current environment");
      (*
      ("-print-cache", Arg.Unit show_cache,
       "Print cache results after typechecking");
      ("-global", Arg.String (fun s -> set_global_object s),
       "<class> use <class> as the global object");
      ("-allow-unbound", Arg.String allow_unbound,
       "Permit unbound global variables, with default type given by the argument");
      ("-assert-typ", Arg.String assert_typ,
       "Assert that all un-annotated assignments have a given type");
      ("-simple-tests", Arg.Unit (set_action SimpleTests.run_tests),
       "Run a suite of simple tests")*)
       ]
end
