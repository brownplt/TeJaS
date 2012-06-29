open Prelude
open Sig
open Css
open ListExt

open Strobe_typ

module type JQUERY_TYPS = sig
  type sel
  type strobeTyp
  type typ = 
    | TForall of string option * id * sigma * typ (* replacement for TForall with only typ bounds *)
    | TApp of typ * sigma list (* replacement for TApp with only typ arguments *)
    | TDom of string option * typ * sel
    | TStrobe of strobeTyp

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

  type strobeKind
  type kind = KMult of kind | KStrobe of strobeKind

  val embed_t : strobeTyp -> typ
  val embed_k : strobeKind -> kind
end

module type JQUERY_TYP = functor (Css : CSS) -> functor (STROBE : TYPS) ->
  (JQUERY_TYPS with type strobeTyp = STROBE.typ with type strobeKind = STROBE.kind with type sel = Css.t)

module type JQUERY_ACTIONS = sig
  type typ
  type kind
  type multiplicity
  module Pretty : sig
    val typ : typ -> FormatExt.printer
    val kind : kind -> FormatExt.printer
    val multiplicity : multiplicity -> FormatExt.printer
    val useNames : bool -> unit
    val shouldUseNames : unit -> bool
  end
  val apply_name : string option -> typ -> typ
  val replace_name : string option -> typ -> typ
  val name_of : typ -> string option
  val free_ids : typ -> IdSet.t
  val free_typ_ids : typ -> IdSet.t
  val free_mult_ids : multiplicity -> IdSet.t
  val rename_avoid_capture : IdSet.t -> id list -> typ -> (id list * typ)
  val canonical_multiplicity : multiplicity -> multiplicity
  val canonical_type : typ -> typ
  val mult_mult_subst : id -> multiplicity -> multiplicity -> multiplicity
  val mult_typ_subst : id -> multiplicity -> typ -> typ
  val typ_mult_subst : id -> typ -> multiplicity -> multiplicity
  val typ_typ_subst : id -> typ -> typ -> typ
end

