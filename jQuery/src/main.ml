open Random
open Format
open FormatExt
open Prelude
open SetExt
module BI = Bare_instantiation
module JQI = JQuery_instantiation
module Actions = BI.Actions

let string_of_cin cin =
  let buf = Buffer.create 5000 in
    Buffer.add_channel buf cin (in_channel_length cin);
    Buffer.contents buf

let mk_flag flag desc (default : bool) =
  let value = ref default in
  let set_flag () = value := not default in
  let get_flag () = !value in
  let spec = (flag, Arg.Unit set_flag, desc) in
    (spec, get_flag)

module Input : sig
  val get_cin : unit -> string
  val get_cin_name : unit -> string
  val set_cin : in_channel -> string -> unit
  val set_re_test_depth : int -> unit
  val get_re_test_depth : unit -> int
  val set_re_test_count : int -> unit
  val get_re_test_count : unit -> int
  val get_sourcetype : unit -> string
  val set_sourcetype : string -> unit -> unit
end = struct

  let re_test_depth = ref None
  let re_test_count = ref None

  let c = ref None
  let str = ref None

  let sourcetype = ref "js"

  let cname = ref "no input specified"

  let get_cin () = match !c with
    | None -> failwith "jst: no input files"
    | Some cin -> cin

  let get_cin_name () = !cname

  let set_cin cin name = match !c with
    | None -> c := Some (string_of_cin cin); cname := name
    | Some _ -> failwith "invalid arguments"

  let set_re_test_depth i = re_test_depth := Some i
  let set_re_test_count i = re_test_count := Some i

  let get_sourcetype () = !sourcetype
  let set_sourcetype (str : string) _ = sourcetype := str

  let get_re_test_depth () = match !re_test_depth with
    | None -> 3
    | Some i -> i

  let get_re_test_count () = match !re_test_count with
    | None -> 100
    | Some i -> i

end

open Input

let (set_simpl_cps, get_simpl_cps) =
  mk_flag "-simplcps" "use simplified, but slower CPS (broken)" false


let action_pretty () : int =
  let prog = JavaScript.parse_javascript (get_cin ()) (get_cin_name ()) in
  JavaScript.Pretty.p_prog prog std_formatter;
  print_newline ();
  0

let action_expr () : int =
  let prog = JavaScript.parse_javascript (get_cin ()) (get_cin_name ()) in
  let e = Exprjs_syntax.from_javascript prog in
  Exprjs.Pretty.p_expr e std_formatter; print_newline();
  print_newline();
  Exprjs.Pretty.p_expr (Exprjs.lift_decls e) std_formatter;
  0


let src_js : JavaScript_syntax.prog option ref = ref None

let get_exprjs () =
  match get_sourcetype () with
    | "js" ->
      let js = JavaScript.parse_javascript (get_cin ()) (get_cin_name ()) in
      (js, Exprjs.lift_decls (Exprjs_syntax.from_javascript js))
    (* | "sb" -> *)
    (*     (parse_sb (get_cin ()) (get_cin_name ())) *)
    | ext -> failwith ("unknown file extension " ^ ext)
  (* let (prog, _) = unique_ids tjs in *)
  (*   Sb_owned.owned_inference prog *)

let action = ref (fun () ->
  failwith "No action set by type-checker")

let is_action_set = ref false

let set_action (thunk : unit -> 'a) (() : unit) : unit =
  if !is_action_set then
    (eprintf "invalid arguments (-help for help)\n"; exit 1)
  else
    (is_action_set := true; action := thunk)

let main () : unit =
  Arg.parse
    ((Actions.provided_actions set_action) @
    [ 
      ("-pretty", Arg.Unit (set_action action_pretty),
       "pretty-print JavaScript");
      ("-expr", Arg.Unit (set_action action_expr),
       "simplify JavaScript to exprjs");
      (* ("-noflows", Arg.Unit disable_flows, *)
      (*  "disable flow analysis (benchmarks and debugging)"); *)
      ("-sb", Arg.Unit (set_sourcetype "sb"),
       "Parse strobe source");
      ("-stdin", Arg.Unit (fun () -> set_cin stdin "<stdin>"),
       "read from stdin instead of a file");
      set_simpl_cps;
    ])
    (fun s -> set_cin (open_in s) s)
    "Usage: jst [options] [file]\noptions are:\n"

let cleanup () =
  pp_print_flush std_formatter ();
  pp_print_flush err_formatter ();;

at_exit cleanup;
Printexc.print main ();
try
  Actions.init_with_asts (get_exprjs ());
  exit (!action ());
with
    Failure s ->  eprintf "%s\n" s; exit 3
  | _ -> eprintf "Unknown failure\n"; exit 4
    (*
  | LJSfromEJS.Not_well_formed (p, s) ->
      eprintf "%s not well-formed:\n%s\n" (Pos.toString p) s; exit 2
  | StrobeSub.Typ_error (p, s) ->
      eprintf "fatal type error at %s: %s\n" (Pos.toString p) (StrobeSub.typ_error_details_to_string s); exit 2
  | Strobe.Kind_error s ->
      eprintf "type error (kinding): %s\n" s; exit 2
  | Desugar.Typ_stx_error s ->
      eprintf "type error (annotation): %s\n" s; exit 2 
  | Desugar.Local_structure_error s ->
    eprintf "local structure error: %s\n" s; exit 2 *)
