open Prelude

module P = Dprle.Set
module TypImpl = JQuery_types.Make (P)

type const = string

module Exp = struct
  type exp =
    | EConst of Pos.t * const
    | EAssertTyp of Pos.t * TypImpl.typ * exp
    | EId of Pos.t * id
    | EApp of Pos.t * exp * exp list
    | EFunc of Pos.t * string option * id list * exp
    | ELet of Pos.t * id * exp * exp
    | ERec of Pos.t * (id * TypImpl.typ * exp) list * exp
    | ESeq of Pos.t * exp * exp
    | ECheat of Pos.t * TypImpl.typ * exp
        
  let pos e = match e with
    | EConst(p, _)
    | EAssertTyp(p, _, _)
    | EId(p, _)
    | EApp(p, _, _)
    | EFunc(p, _, _, _)
    | ELet (p, _, _, _)
    | ERec (p, _, _)
    | ESeq (p, _, _)
    | ECheat(p, _, _) -> p
end

module Pretty : sig
  val exp : Exp.exp -> FormatExt.printer
end = struct
  open Format
  open FormatExt
  open Exp
    
  let typ t = TypImpl.Pretty.typ t
  let rec exp e = match e with
    | EConst(_, c) -> string c
    | EAssertTyp(_, t, e) ->
      parens [hov 1 2 [text "assert-typ"; parens [typ t]; exp e]]
    | EId(_, x) -> text x
    | EApp (_, f, args) -> parens [hov 1 1 (text "app" :: exp f :: map exp args)]
    | EFunc (_, name, args, body) ->
      parens [squish [ text "fun "; 
                       begin match name with None -> empty | Some n -> text n end; 
                       parens [horz (map text args)];
                       exp body]]
    | ELet (_, x, bound, body) ->
      parens [ vert [horz [ text "let";
                            parens (map bind [(x, bound)])];
                     exp body ]]
    | ERec (_, binds, body) ->
      parens [ horz [ text "rec"; parens (map rec_bind binds) ];
               exp body ]
    | ESeq (_, e1, e2) -> parens [hov 1 0 [ text "seq"; exp e1; exp e2 ]]
    | ECheat (_, t, e) -> parens [hov 1 0 [horz [ text "cheat"; typ t]; exp e ]]

  and bind (x, e) = 
    parens [text x; exp e]

  and rec_bind (x, t, e) = 
    parens [text x; text ":"; typ t; exp e]

end

let string_of_exp = FormatExt.to_string Pretty.exp
