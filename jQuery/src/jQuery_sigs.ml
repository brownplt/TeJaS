open Prelude
open Sig
open Css
open ListExt

open Strobe_typ

module type JQUERY_TYPS = sig
  type sel
  type baseTyp
  type typ = 
    | TForall of string option * id * sigma * typ (* replacement for TForall with only typ bounds *)
    | TApp of typ * sigma list (* replacement for TApp with only typ arguments *)
    | TDom of string option * typ * sel
    | TStrobe of baseTyp

  and multiplicity = 
    | MPlain of typ
    | MId of id
    | MZero of multiplicity
    | MOne of multiplicity
    | MZeroOne of multiplicity
    | MOnePlus of multiplicity
    | MZeroPlus of multiplicity
    | MSum of multiplicity * multiplicity
  and sigma = STyp of typ | SMult of multiplicity

  type baseKind
  type kind = KMult of kind | KStrobe of baseKind

  type baseBinding
  type binding = BStrobe of baseBinding | BMultBound of multiplicity * kind

  type env = binding list IdMap.t
end

module type JQUERY_TYP = functor (Css : CSS) -> functor (STROBE : TYPS) ->
  (JQUERY_TYPS 
   with type baseTyp = STROBE.typ
     with type baseKind = STROBE.kind
       with type baseBinding = STROBE.binding
         with type sel = Css.t)

module type JQUERY_ACTIONS = sig
  include JQUERY_TYPS
  module Pretty : sig
    val typ : typ -> FormatExt.printer
    val kind : kind -> FormatExt.printer
    val multiplicity : multiplicity -> FormatExt.printer
    val env : env -> FormatExt.printer list
    val useNames : bool -> unit
    val shouldUseNames : unit -> bool
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
  val free_typ_ids : typ -> IdSet.t
  val free_mult_ids : multiplicity -> IdSet.t
  val free_sigma_ids : sigma -> IdSet.t * IdSet.t
  val rename_avoid_capture : IdSet.t -> id list -> typ -> (id list * typ)
  val equivalent_typ : env -> typ -> typ -> bool
  val equivalent_multiplicity : env -> multiplicity -> multiplicity -> bool
  val equivalent_sigma : env -> sigma -> sigma -> bool
  val canonical_multiplicity : multiplicity -> multiplicity
  val canonical_type : typ -> typ
  val canonical_sigma : sigma -> sigma
  val mult_mult_subst : id -> multiplicity -> multiplicity -> multiplicity
  val mult_typ_subst : id -> multiplicity -> typ -> typ
  val typ_mult_subst : id -> typ -> multiplicity -> multiplicity
  val typ_typ_subst : id -> typ -> typ -> typ
  val string_of_typ : typ -> string
  val string_of_mult : multiplicity -> string
  val string_of_kind : kind -> string
end

module type JQUERY_MODULE = sig
  include JQUERY_ACTIONS
  module Strobe : (Strobe_sigs.STROBE_MODULE
                   with type typ = baseTyp
    with type kind = baseKind
    with type binding = baseBinding
    with type extTyp = typ
    with type extKind = kind
    with type extBinding = binding
    with type env = env)
  module Css : (CSS with type t = sel)
end

module type JQUERY_SUBTYPING = sig
  include JQUERY_ACTIONS
  val subtype_sigma : bool -> env -> sigma -> sigma -> bool
  val subtype_typ : bool -> env -> typ -> typ -> bool
  val subtype_mult : bool -> env -> multiplicity -> multiplicity -> bool
  val subtype : env -> typ -> typ -> bool
end

module type JQUERY_KINDING = sig
  include JQUERY_ACTIONS
  val list_prims : unit -> id list
  val new_prim_typ : string -> unit
  val kind_check_typ : env -> id list -> typ -> kind
  val kind_check_mult : env -> id list -> multiplicity -> kind
  val kind_check_sigma : env -> id list -> sigma -> kind
  val kind_check : env -> id list -> typ -> kind
end

module type JQUERY_TYP_ENV = sig
  include TYP_ENV
  type sigma
  type multiplicity
  val bind_mult_id : id -> multiplicity -> env -> env
  val bind_rec_typ_id : id -> id list -> sigma -> env -> env
  val lookup_id : id -> env -> typ
  val lookup_typ_id : id -> env -> typ * kind
  val lookup_mult_id : id -> env -> multiplicity
end

module type JQUERY_TYPECHECKING = sig
  include JQUERY_ACTIONS
  type exp
  val check : env -> typ option -> exp -> typ -> unit
  val synth : env -> typ option -> exp -> typ
  val disable_flows : unit -> unit
  val bind_forall_vars : env -> typ -> env * typ
  val typecheck : env -> typ option -> exp -> unit
  val trace : string -> (exp -> 'a) -> exp -> 'a
end
