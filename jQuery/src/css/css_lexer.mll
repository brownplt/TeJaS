{
  open Prelude
  open Lexing
  open Css_parser
}

(* Adapted from http://www.w3.org/TR/selectors/ *)

let w = [' ' '\t' '\r' '\n' '\x0C'] (* \xC = \f = formfeed *)

let nonascii = [^'\000'-'\177']
let hex_ch = ['0'-'9' 'a'-'f' 'A'-'F']
let unicode =  '\\'hex_ch hex_ch? hex_ch? hex_ch? hex_ch? hex_ch? ("\r\n"|w)?
let escape = unicode | '\\'[^'\n' '\r' '\x0C' '0'-'9' 'a'-'f' 'A'-'F']
let nmstart =  ['_' 'a'-'z' 'A'-'Z'] | nonascii | escape
let nmchar = ['_' 'a'-'z' 'A'-'Z' '0'-'9' '-'] | nonascii | escape
let ident = ['-']? nmstart (nmchar)*
let name = (nmchar)+
let num = ['0'-'9']+|['0'-'9']*'.'['0'-'9']+
let nl = "\n"| "\r\n" | "\r" | "\x0C"
let string1 = ([^'\n' '\r' '\x0C' '\\' '\"']|'\\' nl | nonascii | escape )*
let string2 = ([^'\n' '\r' '\x0C' '\\' '\'']|'\\' nl | nonascii | escape )*

let four_zeros = '0'? '0'? '0'? '0'?

let d = 'd'|'\\' four_zeros("44"|"64")("\r\n"|w)?
let e = 'e'|'\\' four_zeros("45"|"65")("\r\n"|w)?
let n = 'n'|'\\' four_zeros("4e"|"6e")("\r\n"|w)?|'\\''n'
let o = 'o'|'\\' four_zeros("4f"|"6f")("\r\n"|w)?|'\\''o'
let t = 't'|'\\' four_zeros("54"|"74")("\r\n"|w)?|'\\''t'
let b = 'v'|'\\' four_zeros("58"|"78")("\r\n"|w)?|'\\''v'


rule token = parse
| '\r' | '\n' | "\r\n"      { new_line lexbuf; S }
| ' ' | '\t' | '\x0C'       { S }
| "."                       { DOT }
| "/*"                      { block_comment lexbuf }
| "~="                      { INCLUDES }
| "|="                      { DASHMATCH }
| "^="                      { PREFIXMATCH }
| "$="                      { SUFFIXMATCH }
| "*="                      { SUBSTRINGMATCH }
| ident as x                { IDENT x }
| '"' (string1 as x) '"'    { STRING x }
| '\'' (string2 as x) '\''  { STRING x}
| "#" (name as x)           { HASH x }
| "+"                       { PLUS }
| ">"                       { GREATER }
| ","                       { COMMA }
| "~"                       { TILDE }
| ":"                       { COLON }
| "["                       { LBRACK }
| "]"                       { RBRACK }
| "="                       { EQUALS }
| eof                       { EOF }

and block_comment = parse
  | "*/"                    { token lexbuf }
  | '*'                     { block_comment lexbuf }
  | '\n' | '\r' | "\r\n"    { new_line lexbuf; block_comment lexbuf }
  | [^ '\n' '\r' '*']       { block_comment lexbuf }



(* | ident as x "("       { FUNCTION x } *)
(* | num as x "%"           { PERCENTAGE (float_of_string x) } *)
(* | num as x ident as y     { DIMENSION (float_of_string x, y)} *)
(* | num as x            { NUMBER (float_of_string x) } *)
(* | ":" n o t "("  { NOT } *)
(* | "@" ident as x         { ATKEYWORD x } *)
(* | "|" { PIPE } *)
