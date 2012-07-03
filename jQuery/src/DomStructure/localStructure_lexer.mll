{
  open Prelude
  open Lexing
  open LocalStructure_parser
}

(* Adapted from http://www.w3.org/TR/selectors/ *)

let nonascii = [^'\000'-'\177']
let hex_ch = ['0'-'9' 'a'-'f' 'A'-'F']
let unicode =  '\\'hex_ch hex_ch? hex_ch? hex_ch? hex_ch? hex_ch?
let escape = unicode | '\\'[^'\n' '\r' '\x0C' '0'-'9' 'a'-'f' 'A'-'F']
let nmstart =  ['_' 'a'-'z' 'A'-'Z'] | nonascii | escape
let nmchar = ['_' 'a'-'z' 'A'-'Z' '0'-'9' '-'] | nonascii | escape
let ident = ['-']? nmstart (nmchar)*
let name = (nmchar)+
let num = ['0'-'9']+|['0'-'9']*'.'['0'-'9']+
let nl = "\n"| "\r\n" | "\r" | "\x0C"
let string1 = ([^'\n' '\r' '\x0C' '\\' '\"']|'\\' nl | nonascii | escape )*
let string2 = ([^'\n' '\r' '\x0C' '\\' '\'']|'\\' nl | nonascii | escape )*
let string3 = ([^'\n' '\r' '\x0C' '\\' '{' '}']|'\\' nl | nonascii | escape )*


rule token = parse
| [ ' ' '\t' ] + { token lexbuf }
| '\r' | '\n' | "\r\n" { token lexbuf }
| "/*" { block_comment lexbuf }
(* | '"' (string1 as x) '"' { STRING x } *)
(* | '\'' (string2 as x) '\'' { STRING x} *)
(* | '{' (string3 as x) '}' { STRING x} *)
| "\"\"\"" (string1 as x) "\"\"\"" { DOCSTRING x }
| ":" { COLON }
| "," { COMMA }
| "[" { LBRACK }
| "]" { RBRACK }
| "(" { LPAREN }
| ")" { RPAREN }
| "=" { EQUALS }
| "optional" { OPTIONAL }
| "classes" { CLASSES }
| "ids" { IDS }
| ident as x          { IDENT x }
| eof { EOF }
| "..." { PLACEHOLDER }
| "<" { LANGLE }
| ">" { RANGLE }

and block_comment = parse
  | "*/" { token lexbuf }
  | '*' { block_comment lexbuf }
  | [ '\n' '\r' ]  { block_comment lexbuf }
  | [^ '\n' '\r' '*'] { block_comment lexbuf }
