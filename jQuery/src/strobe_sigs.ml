open Prelude
open Sig


module type STROBE_TYPS = sig
    
  type pat

  type extKind
  type kind = 
    | KStar
    | KArrow of kind list * kind
    | KEmbed of extKind

  type presence = 
    | Inherited
    | Present
    | Maybe
  
  type extTyp
  type typ = 
    | TPrim of string
    | TUnion of string option * typ * typ
    | TInter of string option * typ * typ
    | TArrow of typ list * typ option * typ (* args (including <this>), optional variadic arg, return typ *)
    | TThis of typ
    | TObject of obj_typ
    | TWith of typ * obj_typ
    | TRegex of pat
    | TRef of string option * typ
    | TSource of string option * typ
    | TSink of string option * typ
    | TTop
    | TBot
    | TForall of string option * id * typ * typ (** [TForall (a, s, t)] forall a <: s . t *)
    | TId of id
    | TRec of string option * id * typ 
    | TLambda of string option * (id * kind) list * typ (** type operator *)
    | TApp of typ * typ list (** type operator application *)
    | TFix of string option * id * kind * typ (** recursive type operators *)
    | TUninit of typ option ref (** type of uninitialized variables *)
    | TEmbed of extTyp

  and obj_typ = { 
    fields : (pat * presence * typ) list;
    absent_pat : pat;
    cached_parent_typ : typ option option ref;
    cached_guard_pat : pat option ref;
    cached_cover_pat : pat option ref;
    cached_possible_cover_pat : pat option ref; (* pat Lazy.t *)
  }

  type field = pat * presence * typ

  type extBinding
  type binding = 
      BEmbed of extBinding | BTermTyp of typ | BTypBound of typ * kind | BLabelTyp of typ | BTyvar of kind

  type env = extBinding list IdMap.t
  val proto_str : string

  val proto_pat : pat
  val fields : obj_typ -> field list

  val mk_obj_typ : field list -> pat -> obj_typ
  (** Pattern for absent field *)
  val absent_pat : obj_typ -> pat
  (** includes absent *)
  val cover_pat : obj_typ -> pat
  (** excludes absent *)
  val possible_field_cover_pat : obj_typ -> pat
end

module type STROBE_TYP = functor (Pat : SET) -> functor (EXT : TYPS) ->
  (STROBE_TYPS 
   with type extKind = EXT.kind
     with type extTyp = EXT.typ
       with type extBinding = EXT.binding
         with type pat = Pat.t)

module type STROBE_ACTIONS = sig
  include STROBE_TYPS

  type typ_error_details =
    | TypKind of (typ -> kind -> string) * typ * kind
    | StringTyp of (string -> typ -> string) * string * typ
    | FixedString of string
    | String of (string -> string) * string
    | TypTyp of (typ -> typ -> string) * typ * typ
    | NumNum of (int -> int -> string) * int * int
    | Typ of (typ -> string) * typ
    | Pat of (pat -> string) * pat
    | PatPat of (pat -> pat -> string) * pat * pat
    | PatPatTyp of (pat -> pat -> typ -> string) * pat * pat * typ
    | PatTyp of (pat -> typ -> string) * pat * typ
    | TypTypTyp of (typ -> typ -> typ -> string) * typ * typ * typ


  exception Kind_error of string
  exception Typ_error of Pos.t * typ_error_details

  val typ_error_details_to_string : typ_error_details -> string
  
  val typ_mismatch : Pos.t -> typ_error_details -> unit

  val get_num_typ_errors : unit -> int

  val with_typ_exns : (unit -> 'a) -> 'a

  module Pretty : sig
    val typ : typ -> FormatExt.printer
    val kind : kind -> FormatExt.printer
    val useNames : bool -> unit
    val shouldUseNames : unit -> bool
    val env : env -> FormatExt.printer list
    val simpl_typ : typ -> string
    val simpl_kind : kind -> string
  end
  val apply_name : string option -> typ -> typ
  val replace_name : string option -> typ -> typ


  val string_of_typ : typ -> string
  val string_of_kind : kind -> string

  val name_of : typ -> string option
  val free_ids : typ -> IdSet.t
  val free_typ_ids : typ -> IdSet.t

  val map_reduce_t : (extTyp -> 'a) -> ('b -> 'a -> 'b) -> 'b -> typ -> 'b
  val subst : id option -> typ -> (extTyp -> extTyp) -> typ -> typ
  val typ_subst : id -> typ -> typ -> typ
  val rename_avoid_capture : IdSet.t -> id list -> typ -> (id list * typ)
  val equivalent_typ : env -> typ -> typ -> bool
  val canonical_type : typ -> typ

  val expose_twith : env -> typ -> typ
  val lookup_typ : env -> id -> typ * kind
  val expose : env -> typ -> typ
  val simpl_typ : env -> typ -> typ

  val typ_assoc : env -> typ -> typ -> typ IdMap.t

  val trace : string -> string -> ('a -> bool) -> (unit -> 'a) -> 'a

  (* val merge : typ -> obj_typ -> typ *)

end

module type STROBE_SUBTYPING = sig
  include STROBE_ACTIONS
  val subtype : env -> typ -> typ -> bool

  val pat_env : env -> pat IdMap.t

  val simpl_lookup : Pos.t -> env -> typ -> pat -> typ
  val inherits : Pos.t -> env -> typ -> pat -> typ
  val typ_union : env -> typ -> typ -> typ
  val typ_intersect : env -> typ -> typ -> typ

  val num_cache_hits : unit -> int
  val num_cache_misses : unit -> int
  val print_cache : string -> FormatExt.printer
end

module type STROBE_MODULE = sig
  include STROBE_ACTIONS
  module Ext : (EXT_TYP_ACTIONS
                with type baseTyp = typ
    with type baseKind = kind
    with type baseBinding = binding
    with type env = env
    with type typ = extTyp
    with type kind = extKind
    with type binding = extBinding)
  module Pat : (SET with type t = pat)
end

module type STROBE_KINDING = sig
  include STROBE_TYPS
  val list_prims : unit -> id list
  val new_prim_typ : string -> unit
  val kind_check : env -> id list -> typ -> kind
end

module type STROBE_TYPECHECKING = sig
  include STROBE_ACTIONS
  type exp
  val check : env -> extTyp option -> exp -> typ -> unit
  val synth : env -> extTyp option -> exp -> typ
  val disable_flows : unit -> unit
  val bind_forall_vars : env -> typ -> env * typ
  val typecheck : env -> extTyp option -> exp -> unit
  val trace : string -> ('a -> bool) -> (exp -> 'a) -> exp -> 'a
end
