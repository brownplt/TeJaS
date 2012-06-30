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
    | TIntersect of string option * typ * typ
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
  type binding = BEmbed of extBinding | BTermTyp of typ | BTypBound of typ * kind

  type env = binding IdMap.t
end

module type STROBE_TYP = functor (Pat : SET) -> functor (EXT : TYPS) ->
  (STROBE_TYPS 
   with type extKind = EXT.kind
     with type extTyp = EXT.typ
       with type extBinding = EXT.binding
         with type pat = Pat.t)

module type STROBE_ACTIONS = sig
  type typ
  type kind
  type binding
  type extTyp
  type extKind
  type extBinding
  type pat
  type field
  type obj_typ
  type env
  val name_of : typ -> string option
  val free_ids : typ -> IdSet.t
  val free_typ_ids : typ -> IdSet.t

  val map_reduce_t : (extTyp -> 'a) -> ('b -> 'a -> 'b) -> 'b -> typ -> 'b
  val subst : id option -> typ -> (extTyp -> extTyp) -> typ -> typ
  val rename_avoid_capture : IdSet.t -> id list -> typ -> (id list * typ)
  val equivalent_typ : env -> typ -> typ -> bool

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


  exception Typ_error of Pos.t * typ_error_details
  exception Not_subtype of typ_error_details

  val typ_error_details_to_string : typ_error_details -> string

      

  (* type typenv = (typ * kind) IdMap.t *)

  module Pretty : sig
    val typ : typ -> FormatExt.printer
    val kind : kind -> FormatExt.printer
    val useNames : bool -> unit
    val shouldUseNames : unit -> bool
  end

  val string_of_typ : typ -> string
  val string_of_kind : kind -> string
  
  (* val expose_twith : typenv -> typ -> typ *)

  (* val proto_str : string *)

  (* val proto_pat : pat *)

  val mk_obj_typ : field list -> pat -> obj_typ

  (* val fields : obj_typ -> field list *)

  (* (\** Pattern for absent field *\) *)
  (* val absent_pat : obj_typ -> pat *)

  (* (\** includes absent *\) *)
  (* val cover_pat : obj_typ -> pat *)

  (* (\** excludes absent *\) *)
  (* val possible_field_cover_pat : obj_typ -> pat *)

  (* val merge : typ -> obj_typ -> typ *)

  (* val typ_subst : id -> typ -> typ -> typ *)

  (* val parent_typ : typenv -> typ -> typ option *)

  (* val simpl_typ : typenv -> typ -> typ *)

  val apply_name : string option -> typ -> typ

  val replace_name : string option -> typ -> typ

  (* val expose : typenv -> typ -> typ *)

  (* val simpl_lookup : Pos.t -> typenv -> typ -> pat -> typ *)

  (* val inherits : Pos.t -> typenv -> typ -> pat -> typ *)

  (* val typ_union : typenv -> typ -> typ -> typ *)

  (* val typ_intersect : typenv -> typ -> typ -> typ *)

  (* val subtypes : typenv -> typ list -> typ list -> bool *)

  (* val subtype : typenv -> typ -> typ -> bool *)

  (* val typ_mismatch : Pos.t -> typ_error_details -> unit *)

  (* val get_num_typ_errors : unit -> int *)

  (* val with_typ_exns : (unit -> 'a) -> 'a *)

  (* val pat_env : typenv -> pat IdMap.t *)

  (* (\** [object_typs t] returns a list of object types in a union and a flag *)
  (*     which is set if there were no other types in [t]. *\) *)
  (* val object_typs : typ -> typ list * bool *)

end
