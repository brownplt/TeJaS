open Prelude
open Sig

module type MAIN_ACTIONS = sig
  val provided_actions : ((unit -> int) -> (unit -> unit)) ->
                         (string * Arg.spec * string) list
  val init_with_asts :
    (JavaScript_syntax.prog * Exprjs_syntax.expr) -> unit
  (*
  load_env : string -> unit
  allow_unbound : string -> unit
  set_global_object : string -> unit
  verbose_errors : bool -> unit
  assert_typ : string -> unit
  pre_typecheck : unit -> unit
  typecheck : unit -> unit
  print_typ : string -> unit
  print_env : unit -> unit
  print_cache : unit -> unit
  test : unit -> unit
  *)
end

