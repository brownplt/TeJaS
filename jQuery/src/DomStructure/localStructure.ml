open Prelude
open LocalStructure_syntax

let parseLocalStructure str =
  let module P = LocalStructure_parser in
  let module L = LocalStructure_lexer in
  let lexbuf = Lexing.from_string str in
  try
    lexbuf.Lexing.lex_curr_p <- Lexing.dummy_pos;
    P.decl_group L.token lexbuf
  with
  | Failure "lexing: empty token" ->
    failwith (sprintf "error lexing local structure declarations %s at %s"
                str
                (Pos.rangeToString
                   lexbuf.Lexing.lex_curr_p lexbuf.Lexing.lex_curr_p))
  | LocalStructure_parser.Error ->
    failwith (sprintf "error parsing local structure declarations %s at %s"
                str
                (Pos.rangeToString
                   lexbuf.Lexing.lex_curr_p lexbuf.Lexing.lex_curr_p))

module Pretty : sig
  val p_decl : declComp -> FormatExt.printer
end = struct
  open Format
  open FormatExt
  let cut fmt = pp_print_cut fmt ()
  let rec p_decl d = match d with
    | Decl(name, desc, tyname, (reqClasses, optClasses, ids), content) ->
      let titleline = label (name ^ " : ") (match desc with
        | None -> [text tyname]
        | Some desc -> 
          [text tyname; 
           (enclose 3 "" empty (text "\"\"\"") (text "\"\"\"") [text (String.escaped desc)])]) in
      let attribs = 
        (horzOrVert
           (add_sep_between (text ",")
              [label "required classes (any): "
                  [brackets [inter (fun fmt -> text "," fmt; pp_print_space fmt ())
                                (List.map text reqClasses)]];
               label "optional classes (any): " 
                 [brackets [inter (fun fmt -> text "," fmt; pp_print_space fmt ())
                               (List.map text optClasses)]];
               label "ids (any): " 
                 [brackets [inter (fun fmt -> text "," fmt; pp_print_space fmt ())
                               (List.map text ids)]]])) in
      let body = 
        if content = [] 
        then [titleline; attribs] 
        else [titleline; attribs; vert (List.map p_content content)] in
      parens [vert body]
  and p_content c = match c with
    | DPlaceholder -> text "..."
    | DNested d -> p_decl d
    | DId d -> angles [text d]
end
