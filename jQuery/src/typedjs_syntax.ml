open Prelude
open Sig
open JQuery_syntax

(** Types written by users. *)
module WritTyp = struct

  type t = 
    | Str
    | Bool
    | Prim of string
    | Union of t * t
    | Inter of t * t
    | Arrow of t option * t list * t option * t (** [Arrow (this, args, varargs, result)] *)
    | Object of f list
    | With of t * f list
    | Pat of Pat.t
    | Ref of t
    | Source of t
    | Top
    | Bot
    | This of t
    | TId of id
    | Forall of id * s * t
    | Rec of id * t
    | Syn of id
    | Lambda of (id * k) list * t
    | Fix of id * k * t
    | App of t * s list
       
  and m =
    | Plain of t
    | MId of id
    | Zero of m
    | One of m
    | ZeroOne of m
    | OnePlus of m
    | ZeroPlus of m
    | Sum of m * m

  and s = Typ of t | Mult of m

  and f = 
    | Present of Pat.t * t
    | Maybe of Pat.t * t
    | Inherited of Pat.t * t
    | Absent of Pat.t
    | Skull of Pat.t
    | Star of t option

  and k = KStar | KArrow of k list * k | KMult of k

  let (print_typ, print_mult, print_sigma) = 
    let open FormatExt in
    let rec helper_s s = match s with Mult m -> helper_m m | Typ t -> helper_t t
    and helper_m mult = match mult with
      | Plain t -> helper_t t
      | MId id -> text id
      | Zero m -> squish[text "0"; angles [helper_m m]]
      | One m -> squish[text "1"; angles [helper_m m]]
      | ZeroOne m -> squish[text "01"; angles [helper_m m]]
      | ZeroPlus m -> squish[text "0+"; angles [helper_m m]]
      | OnePlus m -> squish[text "1+"; angles [helper_m m]]
      | Sum (m1, m2) -> squish[text "Sum"; angles [horz[helper_m m1; text "++"]; helper_m m2]]
    and helper_t typ = match typ with
      | Str -> text "Str"
      | Bool -> text "Bool"
      | Prim s -> squish [text "@"; text s]
      | Union (t1, t2) -> parens [horz [helper_t t1; text "+"; helper_t t2]]
      | Inter (t1, t2) -> parens [horz [helper_t t1; text "&"; helper_t t2]]
      | Arrow (this, args, varargs, result) ->
        horz [
          (match this with None -> text "[]" | Some t -> brackets [helper_t t]);
          horz (intersperse (text "*") (map helper_t args));
          (match varargs with None -> text "" | Some t -> horz [text "*"; helper_t t; text "..."]);
          text "=>";
          helper_t result]
      | Object f -> braces [obj f]
      | With (t, f) -> braces[horz [helper_t t; text "with"; obj f]]
      | Pat p -> text (Pat.pretty p)
      | Ref t -> horz [text "Ref"; helper_t t]
      | Source t -> horz [text "Src"; helper_t t]
      | Top -> text "Top"
      | Bot -> text "Bot"
      | TId x -> text x
      | This t -> squish [text "this"; parens [helper_t t]]
      | Forall (x, bound, t) -> horz [text "forall"; text x; text "<:"; helper_s bound; text "."; helper_t t]
      | Rec(x, t) -> horz [text "rec"; text x; text "."; helper_t t]
      | Syn x -> parens [horz [text "Syn"; text x]]
      | Lambda(idkinds, t) -> horz [parens [horz (intersperse (text ",") (map (fun (x, k) -> horz [text x; text "::"; kind k]) idkinds))]; text "=>"; helper_t t]
      | Fix (x, k, t) -> horz [text "fix"; text x; text "::"; kind k; text "."; helper_t t]
      | App (t, args) -> squish [helper_t t; angles [horz (intersperse (text ",") (map helper_s args))]]
    and obj f = vert (map (fun f -> match f with
      | Present(p, t) -> horz [text (Pat.pretty p); text ":!"; helper_t t]
      | Maybe(p, t) -> horz [text (Pat.pretty p); text ":?"; helper_t t]
      | Inherited(p, t) -> horz [text (Pat.pretty p); text ":?"; helper_t t]
      | Absent p -> horz [text (Pat.pretty p); text ": _"]
      | Skull p -> horz [text (Pat.pretty p); text ": BAD"]
      | Star t -> (match t with None -> text "* : _" | Some t -> horz [text "* :?"; helper_t t])) f)
    and kind k = match k with
      | KStar -> text "*"
      | KArrow (ks, k) -> 
        horz [horz (intersperse (text ",") (map pr_kind ks)); text "=>"; kind k]
      | KMult k -> squish [text "M"; angles [kind k]]
    and pr_kind k = match k with
      | KArrow _ -> parens [kind k]
      | _ -> kind k

    in 
    (helper_t, helper_m, helper_s)
    let string_of_typ typ = print_typ typ Format.str_formatter; Format.flush_str_formatter ()
    let mult_of_typ mult = print_mult mult Format.str_formatter; Format.flush_str_formatter ()
    let sigma_of_typ sigma = print_sigma sigma Format.str_formatter; Format.flush_str_formatter ()
                          


end

type env_decl =
  | EnvBind of Pos.t * id * WritTyp.t
  | EnvType of Pos.t * id * WritTyp.t
  | EnvPrim of Pos.t * id
  | RecBind of env_decl list
  | ObjectTrio of Pos.t * (id * WritTyp.t) * (id * WritTyp.t) * (id * WritTyp.t)

type annotation =
  | ATyp of WritTyp.t
  | AUpcast of WritTyp.t
  | ADowncast of WritTyp.t
  | ATypAbs of id * WritTyp.t
  | ATypApp of WritTyp.t list
  | AAssertTyp of WritTyp.t
  | ACheat of WritTyp.t


(* module Typ = struct *)


(*   let rec forall_arrow (typ : TypImpl.typ) : (id list * TypImpl.typ) option = match typ with *)
(*     | TypImpl.TArrow _ -> Some ([], typ) *)
(*     | TypImpl.TForall (_, x, _, typ') -> begin match forall_arrow typ' with *)
(*       | None -> None *)
(*       | Some (xs, t) -> Some (x :: xs, t) *)
(*     end *)
(*     | TypImpl.TRec (_, x, t) -> forall_arrow (TypImpl.typ_typ_subst x typ t) *)
(*     | _ -> None *)

(*   let rec match_func_typ (typ : TypImpl.typ) : (TypImpl.typ list * TypImpl.typ option * TypImpl.typ) option = match typ with *)
(*     | TypImpl.TForall (_, _, _, t) -> match_func_typ t *)
(*     | TypImpl.TArrow (_, args, varargs, ret) -> Some (args, varargs, ret) *)
(*     | _ -> None *)

(*   (\* let is_present (fld : TypImpl.field) = match fld with *\) *)
(*   (\*   | (_, TypImpl.Present, _) -> true *\) *)
(*   (\*   | _ -> false *\) *)

(* end *)

