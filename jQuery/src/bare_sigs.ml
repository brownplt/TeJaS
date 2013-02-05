open Prelude
open Sig
open ListExt

open Strobe_typ

module type BARE_TYPS = sig
  type baseTyp

  type baseKind
  type kind = KStrobe of baseKind

  type typ = 
    | TStrobe of baseTyp

  type baseBinding
  type binding = BStrobe of baseBinding

  type env = binding list IdMap.t
end

module type BARE_TYP = functor (STROBE : TYPS) ->
  (BARE_TYPS 
   with type baseTyp = STROBE.typ
     with type baseKind = STROBE.kind
       with type baseBinding = STROBE.binding)

module type BARE_ACTIONS = sig
  include BARE_TYPS
  module Pretty : sig
    val typ : typ -> FormatExt.printer
    val kind : kind -> FormatExt.printer
    val env : env -> FormatExt.printer list
    val useNames : bool -> unit
    val shouldUseNames : unit -> bool
    val simpl_typ : typ -> string
    val simpl_kind : kind -> string
  end
  val extract_t : typ -> baseTyp
  val extract_k : kind -> baseKind
  val extract_b : binding -> baseBinding
  val embed_t : baseTyp -> typ
  val embed_k : baseKind -> kind
  val embed_b : baseBinding -> binding
  val unwrap_t : typ -> typ
  val unwrap_k : kind -> kind
  val unwrap_b : binding -> binding
  val unwrap_bt : baseTyp -> baseTyp
  val unwrap_bk : baseKind -> baseKind
  val unwrap_bb : baseBinding -> baseBinding
  val apply_name : string option -> typ -> typ
  val replace_name : string option -> typ -> typ
  val name_of : typ -> string option
  val free_ids : typ -> IdSet.t
  val rename_avoid_capture : IdSet.t -> id list -> typ -> (id list * typ)
  val equivalent_typ : env -> typ -> typ -> bool
  val canonical_type : typ -> typ
  val collapse_if_possible : env -> typ -> typ
  val typ_subst : id -> typ -> typ -> typ
  val string_of_typ : typ -> string
  val string_of_kind : kind -> string
  val simpl_typ : env -> typ -> typ
  val typ_assoc : env -> typ -> typ -> binding IdMap.t
end

module type BARE_MODULE = sig
  include BARE_ACTIONS
  module Strobe : (Strobe_sigs.STROBE_MODULE
                   with type typ = baseTyp
    with type kind = baseKind
    with type binding = baseBinding
    with type extTyp = typ
    with type extKind = kind
    with type extBinding = binding
    with type env = env)
end

module type BARE_SUBTYPING = sig
  include BARE_ACTIONS
  val subtype_typ : bool -> env -> typ -> typ -> bool
  val subtype : env -> typ -> typ -> bool
  val num_cache_hits : unit -> int
  val num_cache_misses : unit -> int
  val print_cache : string -> FormatExt.printer
  val project_typs : typ -> typ -> env -> env
end

module type BARE_KINDING = sig
  include BARE_ACTIONS
  val list_prims : unit -> id list
  val new_prim_typ : string -> unit
  val kind_check_typ : env -> id list -> typ -> kind
  val kind_check : env -> id list -> typ -> kind
end

module type BARE_TYP_ENV = sig
  include TYP_ENV
  val do_use_strict_selections : unit -> unit
end

module type BARE_TYPECHECKING = sig
  include BARE_ACTIONS
  type exp
  val check : env -> typ option -> exp -> typ -> unit
  val synth : env -> typ option -> exp -> typ
  val disable_flows : unit -> unit
  val bind_forall_vars : env -> typ -> env * typ
  val typecheck : env -> typ option -> exp -> unit
  val trace : string -> ('a -> bool) -> (exp -> 'a) -> exp -> 'a
  val forall_arrow : typ -> ((id * binding) list * typ) option
  val assoc_sub : env -> typ -> typ -> (Pos.t -> (id * binding) list -> typ -> typ)
end

