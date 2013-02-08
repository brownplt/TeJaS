open Prelude
open Format
open FormatExt
open Bare_syntax
open Main_actions

module B = BareImpl
module S = StrobeImpl
module BareDesugar = Bare_desugar.Make (StrobeMod) (BareMod)
module SEnv = Strobe_env.Make (StrobeMod) (Strobe_kind) (BareDesugar)
module BareEnv = Bare_env.MakeExt (BareMod) (Bare_kind) (SEnv) (BareDesugar)

module rec BareSub : (Bare_sigs.BARE_SUBTYPING
                        with type typ = BareImpl.typ
  with type kind = BareImpl.kind
  with type binding = BareImpl.binding
  with type env = BareImpl.env
  with type baseTyp = BareImpl.baseTyp
  with type baseKind = BareImpl.baseKind
  with type baseBinding = BareImpl.baseBinding) =
  Bare_subtyping.MakeActions (StrobeSub) (BareMod) (BareEnv)
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
  Strobe_subtyping.MakeActions (StrobeMod) (BareSub) (BareEnv)


module DummySemicfa = struct
  type env = BareEnv.env
  type exp = Exp.exp
  let semicfa _ _ e = e
end
module DummyStatic = struct
  type typ = BareEnv.typ
  type env = BareEnv.env
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
  Strobe_typechecking.Make (StrobeMod) (Exp) (BareEnv) (StrobeSub) (Bare_kind) (DummySemicfa) (DummyStatic) (BareTC)
and BareTC : (Bare_sigs.BARE_TYPECHECKING
                       with type typ = BareImpl.typ
  with type kind = BareImpl.kind
  with type binding = BareImpl.binding
  with type env = BareImpl.env
  with type baseTyp = BareImpl.baseTyp
  with type baseKind = BareImpl.baseKind
  with type baseBinding = BareImpl.baseBinding
  with type exp = Exp.exp) =
  Bare_typechecking.Make (BareMod) (Exp) (BareEnv) (BareSub) (Bare_kind) (StrobeTC)

module WeaveAnnotations = Bare_weaveAnnotations.Make (Exp) (BareDesugar)
module LJSfromEJS = Typedjs_fromExpr.Make (Exp)

module Actions : MAIN_ACTIONS = struct

  let src_js : JavaScript_syntax.prog option ref = ref None
  let src_ljs : Exprjs_syntax.expr option ref = ref None
  let init_with_asts (js, ljs) =
    src_js := Some js;
    src_ljs := Some ljs

  let env : BareEnv.env ref = ref IdMap.empty
  let global_object = ref None

  let load_env (fname : string) : unit =
    env := BareEnv.extend_global_env !env (BareEnv.parse_env_file (open_in fname) fname)

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

  let actual_data () =
    let open Typedjs_writtyp.WritTyp in
    let env =
      BareEnv.set_global_object (get_env ()) (get_global_object ()) in
      (* let typ_vars = Unidl.unidl !idl_defs in *)
      (* Typedjs_env.set_global_object *)
      (*   (extend_env IdMap.empty typ_vars (get_env ())) *)
      (*   (get_global_object ()) in *)
    let typedjs = get_typedjs () in
    let new_decls = ReadTyps.new_decls (List.rev !JavaScript_lexer.comments) in
    let env = BareEnv.extend_global_env env new_decls in
    set_env env;
    let annot_js = weave_annotations typedjs in
    (env, annot_js)

  let default_typ : B.typ option ref = ref None

  let action_tc () : int = timefn "Typechecking" (fun () ->
    let (env, asserted_js) = actual_data () in
    BareTC.typecheck env !default_typ asserted_js;
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

  let provided_actions set_action = [
      ("-env", Arg.String (fun s -> load_env s),
       "<file> read environment types from <file>");
      ("-tc", Arg.Unit (set_action action_tc),
       "type-check the source program (default when no options are given)");
      ("-pretc", Arg.Unit (set_action action_pretypecheck),
       "basic well-formedness checks before type-checking and flow-analysis");
      ("-print-typ", Arg.String (fun ty ->
        let (typ, _) = BareEnv.lookup_typ_id ty (get_env ()) in
        horz [text ty; text "="; BareMod.Pretty.typ (BareMod.replace_name None typ)] std_formatter;
        Format.pp_print_flush std_formatter ()),
       "Print the definition of a single type");
      ("-verbose-errors", Arg.Unit (fun () -> BareMod.Pretty.useNames false),
       "Print types structurally, rather than with pretty names");
      (*
      ("-print-cache", Arg.Unit show_cache,
       "Print cache results after typechecking");
      ("-global", Arg.String (fun s -> set_global_object s),
       "<class> use <class> as the global object");
      ("-allow-unbound", Arg.String allow_unbound,
       "Permit unbound global variables, with default type given by the argument");
      ("-assert-typ", Arg.String assert_typ,
       "Assert that all un-annotated assignments have a given type");
      ("-print-env", Arg.Unit set_print_env,
       "Print the current environment");
      ("-simple-tests", Arg.Unit (set_action SimpleTests.run_tests),
       "Run a suite of simple tests")*)
       ]
end
