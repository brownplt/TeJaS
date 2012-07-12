{
  open Prelude
  open Lexing
  open Typedjs_parser

  let string_buf = Buffer.create 100

  let get_string () = 
    let s = Buffer.contents string_buf in
    Buffer.clear string_buf;
    s

}

(* Adapted from http://www.w3.org/TR/selectors/ *) 
let nonascii = [^'\000'-'\177']
let hex_ch = ['0'-'9' 'a'-'f' 'A'-'F']
let unicode =  '\\'hex_ch hex_ch? hex_ch? hex_ch? hex_ch? hex_ch?
let escape = unicode | '\\'[^'\n' '\r' '\x0C' '0'-'9' 'a'-'f' 'A'-'F']
let nmstart =  ['_' 'a'-'z' 'A'-'Z'] | nonascii | escape
let nmchar = ['_' 'a'-'z' 'A'-'Z' '0'-'9' '-'] | nonascii | escape
let sel_ident = ['-']? nmstart (nmchar)*
let nl = "\n"| "\r\n" | "\r" | "\x0C"
let string1 = ([^'\n' '\r' '\x0C' '\\' '\"']|'\\' nl | nonascii | escape )*

let ident = ['a'-'z' 'A'-'Z' '$' '_' '%']([ 'a'-'z' 'A'-'Z' '0'-'9' '$' '_']*)

let blank = [ ' ' '\t' '\r' ]

let hex = ['0'-'9' 'A'-'f' 'a'-'f']

let escape_sequence = [^ '\r' '\n'] | ('x' hex hex) | ('u' hex hex hex hex)

let double_quoted_string_char = [^ '\r' '\n' '"' '\\'] | ('\\' escape_sequence)

rule token = parse
   | blank + { token lexbuf }
   | '\n' { new_line lexbuf; token lexbuf }
   | '\r' { new_line lexbuf; token lexbuf }
   | "\r\n" { new_line lexbuf; token lexbuf }
   | "/*" { block_comment lexbuf }
   | "//"[^ '\r' '\n']* [ '\r' '\n' ] { new_line lexbuf; token lexbuf }

   | "..." { DOTS }
   | "->" { ARROW }
   | "=>" { THICKARROW }
   | "(" { LPAREN }
   | ")" { RPAREN }
   | "#{" { HASHBRACE }
   | "{" { LBRACE }
   | "{{" { LLBRACE }
   | "}}" { RRBRACE }
   | "}" { RBRACE }
   | "[" { LBRACK }
   | "]" { RBRACK }
   | "<" { LANGLE }
   | ">" { RANGLE }
   | "," { COMMA }
   | ";" { SEMI }
   | "M" { MULT }
   | "0" { ZERO }
   | "1" { ONE }
   | "01" { ZEROONE }
   | "0+" { ZEROPLUS }
   | "1+" { ONEPLUS }
   | "Sum" { SUM }
   | "Any" { ANY }
   | "Str" { STR }
   | "Bool" { BOOL }
   | "Num" { PRIM "Num" }
   | "True" { PRIM "True" }
   | "False" { PRIM "False" }
   | "Undef" { PRIM "Undef" }
   | "Unsafe" { PRIM "Unsafe" }
   | "Mutable" { PRIM "Mutable" }
   | "Immutable" { PRIM "Immutable" }
   | "Constructing" { PRIM "Constructing" }
   | "Null" { PRIM "Null" }
   | "@" (ident as x) { PRIM x }
   | "_" { UNDERSCORE }
   | "BAD" { BAD }
   | "ref" { REF }
   | "*" { STAR }
   | ":" { COLON }
   | "::" { COLONCOLON }
   | "+" { UNION }
   | "&" { INTERSECTION }
   | "." { DOT }
   | "=" { EQUALS }
   | "upcast" { UPCAST }
   | "downcast" { DOWNCAST }
   | "operator" { OPERATOR }
   | "this" { THIS }
   | "is" { IS }
   | "cheat" { CHEAT }
   | "val" { VAL }
   | "forall" { FORALL }
   | "type" { TYPE }
   | "typlambda" { TYPLAMBDA }
   | "typrec" { TYPREC }
   | "and" { AND }
   | "constructor" { CONSTRUCTOR }
   | "prototype" { PROTOTYPE }
   | "instance" { INSTANCE }
   | "<:" { LTCOLON }
   | "?" { QUES }
   | "^" { CARET }
   | "!" { BANG }
   | "rec" { REC }
   | "primitive" { PRIMITIVE }
   | "with" { WITH }
   | "\"\"\"" (string1 as x) "\"\"\"" { DOCSTRING x }
   | "optional" { OPTIONAL }
   | "classes" { CLASSES }
   | "ids" { IDS }
   | eof { EOF }
   | ident as x { ID x }
   | '"' (double_quoted_string_char* as x) '"' { STRING x }
   | '\''(ident as x) { TID x }
   | '/' { regexp lexbuf }



and block_comment = parse
  | "*/" { token lexbuf }
  | '*' { block_comment lexbuf }
  | "\r\n" { new_line lexbuf; block_comment lexbuf }
  | [ '\n' '\r' ]  { new_line lexbuf; block_comment lexbuf }
  | [^ '\n' '\r' '*'] { block_comment lexbuf }

and regexp = parse
  | "/" { REGEX (get_string ()) }
  | '\\' (_ as ch) { Buffer.add_char string_buf ch; regexp lexbuf }
  | _ as ch { Buffer.add_char string_buf ch; regexp lexbuf }
