open Prelude

module type EQ = sig

  type t

  val is_equal : t -> t -> bool

end

module type PAT = sig
    
  (** string patterns *)
  type t

  val parse : Lexing.position -> string -> t
    
  val singleton : string -> t
  val singleton_string : t -> string option
    
  val empty : t
  val all : t
    
  val intersect : t -> t -> t
  val intersections : t list -> t
  val union : t -> t -> t
  val unions : t list -> t
  val star : t -> t
  val range : (char * char) list -> t
  val negate : t -> t
  val subtract : t -> t -> t
  val concat : t -> t -> t

    
  val is_empty : t -> bool

  val is_overlapped : t -> t -> bool
    
  (** [is_subset pat1 pat2] is true if all strings in [pat1] are also in 
      [pat2]. *)
  val is_subset :t -> t -> bool

  val is_equal : t -> t -> bool

  (** [example pat] returns an example of a string in [pat]. *)
  val example : t -> string option

  val pretty : t -> string
end

module type SET = sig

  (** Type of sets *)
  type t

  val empty : t
  val all : t
    
  val intersect : t -> t -> t
  val intersections : t list -> t
  val union : t -> t -> t
  val unions : t list -> t
  val negate : t -> t
  val subtract : t -> t -> t
  val singleton : string -> t
  val singleton_string : t -> string option
  val var : string -> t


  val pretty : t -> string

  val is_empty : t -> bool
  val is_overlapped : t -> t -> bool
  val is_subset : t IdMap.t -> t -> t -> bool
  val is_equal : t -> t -> bool

  (** [example pat] returns an example of a string in [pat]. *)
  val example : t -> string option

  val parse : Lexing.position -> string -> t

end

module type TYPS = sig
  type typ
  type kind
  type binding
  type env
end

module type TYP_ACTIONS = sig
  include TYPS
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
  val typ_subst : string -> typ -> typ -> typ
  val name_of : typ -> string option
  val free_ids : typ -> IdSet.t
  val equivalent_typ : env -> typ -> typ -> bool
  val rename_avoid_capture : (* free *) IdSet.t -> (* to rename *) id list -> (* in type *) typ -> (id list * typ)
  val canonical_type : typ -> typ
  val collapse_if_possible : env -> typ -> typ
  val string_of_typ : typ -> string
  val string_of_kind : kind -> string
end

module type EXT_TYP_ACTIONS = sig
  include TYP_ACTIONS
  type baseTyp
  type baseKind
  type baseBinding
  val embed_t : baseTyp -> typ
  val embed_k : baseKind -> kind
  val embed_b : baseBinding -> binding
  val extract_t : typ -> baseTyp
  val extract_k : kind -> baseKind
  val extract_b : binding -> baseBinding
  val unwrap_t : typ -> typ
  val unwrap_k : kind -> kind
  val unwrap_b : binding -> binding
  val unwrap_bt : baseTyp -> baseTyp
  val unwrap_bk : baseKind -> baseKind
  val unwrap_bb : baseBinding -> baseBinding
  val simpl_typ : env -> typ -> typ
  val typ_assoc : env -> typ -> typ -> binding IdMap.t
end

module type EXT_TYP_SUBTYPING = sig
  include EXT_TYP_ACTIONS
  val subtype : env -> typ -> typ -> bool
  val project_typs : typ -> typ -> env -> env
  val unfold_typdefs : env -> typ -> typ
end

module type EXT_KINDING = sig
  include EXT_TYP_ACTIONS
  val list_prims : unit -> id list
  val new_prim_typ : string -> unit
  val kind_check : env -> id list -> typ -> kind
end

module type SEMICFA = sig
  type env
  type exp
  val semicfa : IdSet.t -> env -> exp -> exp
end

module type TYPECHECKING = sig
  include TYP_ACTIONS
  type exp
  val check : env -> typ option -> exp -> typ -> unit
  val synth : env -> typ option -> exp -> typ
  val check_app : env -> typ option -> exp -> exp list -> typ -> typ
  val disable_flows : unit -> unit
  val bind_forall_vars : env -> typ -> env * typ
  val typecheck : env -> typ option -> exp -> unit
  val forall_arrow : typ -> ((id * binding) list * typ) option
end

module type EXT_TYPECHECKING = sig
  include EXT_TYP_ACTIONS
  type exp
  val check : env -> typ option -> exp -> typ -> unit
  val synth : env -> typ option -> exp -> typ
  val check_app : env -> typ option -> exp -> exp list -> typ -> typ
  val disable_flows : unit -> unit
  val typecheck : env -> typ option -> exp -> unit
  val bind_forall_vars : env -> typ -> env * typ
  val forall_arrow : typ -> ((id * binding) list * typ) option
  val assoc_sub  : env -> typ -> typ -> (Pos.t -> (id * binding) list -> typ -> typ)
end

module type TYP_ENV = sig
  type typ
  type kind
  type binding
  type env
  type env_decl
  val print_env : env -> FormatExt.printer
  val bind : id -> binding -> env -> env
  val bind_id : id -> typ -> env -> env
  val bind_typ_id : id -> typ -> env -> env
  val bind_lbl : id -> typ -> env -> env
  val clear_labels : env -> env
  val lookup_id : id -> env -> typ
  val lookup_typ_id : id -> env -> typ * kind
  val lookup_typ_alias : id -> env -> typ * kind
  val lookup_lbl : id -> env -> typ
  val parse_env_buf : Lexing.lexbuf -> string -> env_decl list
  val parse_env : string -> string -> env_decl list
  val parse_env_file : in_channel -> string -> env_decl list
  val extend_global_env : env -> env_decl list -> env
  val set_global_object : env -> string -> env
end

module type DESUGAR = sig
  type typ
  type writtyp
  exception Typ_stx_error of string
  val desugar_typ : Pos.t -> writtyp -> typ
end

