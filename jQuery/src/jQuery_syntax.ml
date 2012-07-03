open Prelude
open Sig

module Pat = Dprle.Set
module Css = Css.RealCSS
module rec StrobeImpl : (Strobe_sigs.STROBE_TYPS
                         with type extKind = JQueryImpl.kind
  with type extTyp = JQueryImpl.typ
  with type extBinding = JQueryImpl.binding
  with type pat = Pat.t) = Strobe_typ.Make (Pat) (JQueryImpl)
and JQueryImpl : (JQuery_sigs.JQUERY_TYPS
               with type baseTyp = StrobeImpl.typ
  with type baseKind = StrobeImpl.kind
  with type baseBinding = StrobeImpl.binding
  with type sel = Css.t) = JQuery_types.Make (Css) (StrobeImpl)

module rec JQuery : (JQuery_sigs.JQUERY_ACTIONS
                     with type typ = JQueryImpl.typ
  with type kind = JQueryImpl.kind
  with type multiplicity = JQueryImpl.multiplicity
  with type sigma = JQueryImpl.sigma
  with type binding = JQueryImpl.binding
  with type env = JQueryImpl.env
  with type baseTyp = JQueryImpl.baseTyp
  with type baseKind = JQueryImpl.baseKind
  with type baseBinding = JQueryImpl.baseBinding
  with type sel = JQueryImpl.sel) =
  JQuery_types.MakeActions (Strobe) (JQueryImpl) (Css)
and Strobe : (Strobe_sigs.STROBE_ACTIONS
              with type typ = StrobeImpl.typ
  with type kind = StrobeImpl.kind
  with type binding = StrobeImpl.binding
  with type extTyp = StrobeImpl.extTyp
  with type extKind = StrobeImpl.extKind
  with type extBinding = StrobeImpl.extBinding
  with type pat = StrobeImpl.pat
  with type obj_typ = StrobeImpl.obj_typ
  with type presence = StrobeImpl.presence
  with type env = StrobeImpl.env) =
  Strobe_typ.MakeActions (Pat) (StrobeImpl) (JQuery)

module JQueryMod = JQuery_types.MakeModule (Strobe) (Css) (JQuery)
module StrobeMod = Strobe_typ.MakeModule (Pat) (Strobe) (JQuery)

module rec JQuery_kind : (JQuery_sigs.JQUERY_KINDING
                             with type typ = JQuery.typ
  with type kind = JQuery.kind
  with type multiplicity = JQuery.multiplicity
  with type sigma = JQuery.sigma
  with type binding = JQuery.binding
  with type baseTyp = JQuery.baseTyp
  with type baseKind = JQuery.baseKind
  with type baseBinding = JQuery.baseBinding
  with type env = JQuery.env
  with type sel = JQuery.sel)
  = JQuery_kinding.Make (JQueryMod) (Strobe_kind)
and Strobe_kind : (Strobe_sigs.STROBE_KINDING
         with type typ = Strobe.typ
  with type kind = Strobe.kind
  with type binding = Strobe.binding
  with type extTyp = Strobe.extTyp
  with type extKind = Strobe.extKind
  with type extBinding = Strobe.extBinding
  with type obj_typ = Strobe.obj_typ
  with type presence = Strobe.presence
  with type pat = Pat.t
  with type env = Strobe.env)
  = Strobe_kinding.Make (StrobeMod) (JQuery_kind)

module rec JQuerySub : (JQuery_sigs.JQUERY_SUBTYPING
                     with type typ = JQueryImpl.typ
  with type kind = JQueryImpl.kind
  with type multiplicity = JQueryImpl.multiplicity
  with type binding = JQueryImpl.binding
  with type env = JQueryImpl.env
  with type baseTyp = JQueryImpl.baseTyp
  with type baseKind = JQueryImpl.baseKind
  with type baseBinding = JQueryImpl.baseBinding) =
  JQuery_subtyping.MakeActions (StrobeSub) (JQueryMod)
and StrobeSub : (Strobe_sigs.STROBE_SUBTYPING
              with type typ = StrobeImpl.typ
  with type kind = StrobeImpl.kind
  with type binding = StrobeImpl.binding
  with type extTyp = StrobeImpl.extTyp
  with type extKind = StrobeImpl.extKind
  with type extBinding = StrobeImpl.extBinding
  with type pat = StrobeImpl.pat
  with type obj_typ = StrobeImpl.obj_typ
  with type presence = StrobeImpl.presence
  with type env = StrobeImpl.env) =
  Strobe_subtyping.MakeActions (StrobeMod) (JQuerySub)


type const = string

(* module Exp = struct *)
(*   type exp = *)
(*     | EConst of Pos.t * const *)
(*     | EAssertTyp of Pos.t * JQueryImpl.typ * exp *)
(*     | EId of Pos.t * id *)
(*     | EApp of Pos.t * exp * exp list *)
(*     | EFunc of Pos.t * string option * id list * exp *)
(*     | ELet of Pos.t * id * exp * exp *)
(*     | ERec of Pos.t * (id * JQueryImpl.typ * exp) list * exp *)
(*     | ESeq of Pos.t * exp * exp *)
(*     | ECheat of Pos.t * JQueryImpl.typ * exp *)
        
(*   let pos e = match e with *)
(*     | EConst(p, _) *)
(*     | EAssertTyp(p, _, _) *)
(*     | EId(p, _) *)
(*     | EApp(p, _, _) *)
(*     | EFunc(p, _, _, _) *)
(*     | ELet (p, _, _, _) *)
(*     | ERec (p, _, _) *)
(*     | ESeq (p, _, _) *)
(*     | ECheat(p, _, _) -> p *)
(* end *)

(* module Pretty : sig *)
(*   val exp : Exp.exp -> FormatExt.printer *)
(* end = struct *)
(*   open Format *)
(*   open FormatExt *)
(*   open Exp *)
    
(*   let typ t = JQueryImpl.Pretty.typ t *)
(*   let rec exp e = match e with *)
(*     | EConst(_, c) -> string c *)
(*     | EAssertTyp(_, t, e) -> *)
(*       parens [hov 1 2 [text "assert-typ"; parens [typ t]; exp e]] *)
(*     | EId(_, x) -> text x *)
(*     | EApp (_, f, args) -> parens [hov 1 1 (text "app" :: exp f :: map exp args)] *)
(*     | EFunc (_, name, args, body) -> *)
(*       parens [squish [ text "fun ";  *)
(*                        begin match name with None -> empty | Some n -> text n end;  *)
(*                        parens [horz (map text args)]; *)
(*                        exp body]] *)
(*     | ELet (_, x, bound, body) -> *)
(*       parens [ vert [horz [ text "let"; *)
(*                             parens (map bind [(x, bound)])]; *)
(*                      exp body ]] *)
(*     | ERec (_, binds, body) -> *)
(*       parens [ horz [ text "rec"; parens (map rec_bind binds) ]; *)
(*                exp body ] *)
(*     | ESeq (_, e1, e2) -> parens [hov 1 0 [ text "seq"; exp e1; exp e2 ]] *)
(*     | ECheat (_, t, e) -> parens [hov 1 0 [horz [ text "cheat"; typ t]; exp e ]] *)

(*   and bind (x, e) =  *)
(*     parens [text x; exp e] *)

(*   and rec_bind (x, t, e) =  *)
(*     parens [text x; text ":"; typ t; exp e] *)

(* end *)

(* let string_of_exp = FormatExt.to_string Pretty.exp *)
