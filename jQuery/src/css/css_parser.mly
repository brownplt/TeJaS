%{
  open Prelude
  open Css_syntax

  let concat s c tl =
    match tl with
    | [] -> failwith "impossible"
    |(_, h)::tl' -> (Desc, s)::(c,h)::tl'

(* adapted from http://www.w3.org/TR/selectors/ *)
%}

%token <string> STRING
(* %token <string> FUNCTION *)
%token <string> IDENT
(* %token <float> NUMBER *)
(* %token <float> PERCENTAGE *)
(* %token <num * string> DIMENSION *)
%token <string> HASH
(* %token <string> ATKEYWORD *)
%token INCLUDES DASHMATCH PREFIXMATCH SUFFIXMATCH SUBSTRINGMATCH EQUALS LBRACK RBRACK
       PLUS GREATER COMMA TILDE STAR COLON EOF S DOT


%start selectors_group
%start selector

%type <Css_syntax.regsel list> selectors_group
%type <Css_syntax.regsel> selector

%%

selectors_group
 : separated_nonempty_list(comma_space, selector_no_eof) EOF { $1 }

comma_space : COMMA S* { () }

selector
 : s=selector_no_eof EOF { s }

selector_no_eof
 : s=simple_selector_sequence { [(Desc, s)] }
 | s=simple_selector_sequence S* PLUS S* rest=selector_no_eof { concat s Adj rest }
 | s=simple_selector_sequence S* GREATER S* rest=selector_no_eof { concat s Kid rest }
 | s=simple_selector_sequence S* TILDE S* rest=selector_no_eof { concat s Sib rest }
 | s=simple_selector_sequence S+ rest=selector_no_eof { concat s Desc rest }

simple_selector_sequence :
| sel=simple_sel attrs=list(simple_sel_attribs) { let (s, a) = sel in (s, a @ attrs) }

simple_sel :
| t=type_selector { (t, []) }
| u=universal { (u, []) }
| a=simple_sel_attribs { (USel, [a]) }

simple_sel_attribs :
| h=HASH { SpId h }
| DOT c=IDENT { SpClass c }
| a=attrib { a }
| p=pseudo { SpPseudo p }

type_selector :
| e=element_name { TSel e } (* namespace_prefix?  *)

(* namespace_prefix : *)
(* | IDENT PIPE { TSel $1 } *)
(* | STAR PIPE { USel } *)
(* | PIPE { USel } *)

element_name :
| IDENT { $1 }

universal :
| STAR { USel }  (* namespace_prefix?  *)

attrib :
| LBRACK attr=IDENT value=attrib_value? RBRACK { SpAttrib(attr, value) } (* namespace_prefix?  *)

attrib_value :
| op=attrib_oper v=IDENT { (op, v) }
| op=attrib_oper v=STRING { (op, v) }

attrib_oper :
| PREFIXMATCH { AOStartsWith }
| SUFFIXMATCH { AOEndsWith }
| SUBSTRINGMATCH { AOSubstring }
| EQUALS { AOEquals }
| INCLUDES { AOContainsClass }
| DASHMATCH { AOPrefixedWith }

pseudo :
| COLON COLON? p=IDENT { p }

(*  functional_pseudo *)
(*   : FUNCTION S* expression ')' *)
(*   ; *)

(* expression *)
(*   /* In CSS3, the expressions are identifiers, strings, */ *)
(*   /* or of the form "an+b" */ *)
(*   : [ [ PLUS | '-' | DIMENSION | NUMBER | STRING | IDENT ] S* ]+ *)
(*   ; *)

(* negation *)
(*   : NOT S* negation_arg S* ')' *)
(*   ; *)

(* negation_arg *)
(*   : type_selector | universal | HASH | class | attrib | pseudo *)
(*   ; *)

%%
