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
