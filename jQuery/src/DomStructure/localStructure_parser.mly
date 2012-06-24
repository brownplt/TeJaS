%{
  open Prelude
  open LocalStructure_syntax

  let concat (r1, o1, i1) (r2, o2, i2) = (r1 @ r2, o1 @ o2, i1 @ i2)

%}

%token<string> IDENT DOCSTRING
%token LPAREN RPAREN LBRACK RBRACK LANGLE RANGLE EQUALS EOF
       CLASSES OPTIONAL IDS COLON COMMA PLACEHOLDER 

%start decl_group

%type<LocalStructure_syntax.declSyntax> decl_group

%%

decl_group : nonempty_list(decl) EOF { $1 }

decl :
| LPAREN declname=IDENT COLON desc=DOCSTRING? tyname=IDENT attribs=attribs body=list(body_item) RPAREN
    { Decl(declname, desc, tyname, attribs, body) }

attribs :
| attribs=nonempty_list(attrib) { List.fold_left concat ([], [], []) attribs }

attrib :
| CLASSES EQUALS LBRACK cs=separated_nonempty_list(COMMA, IDENT) RBRACK { (cs, [], []) }
| OPTIONAL CLASSES EQUALS LBRACK cs=separated_nonempty_list(COMMA, IDENT) RBRACK { ([], cs, []) }
| IDS EQUALS LBRACK ids=separated_nonempty_list(COMMA, IDENT) RBRACK { ([], [], ids) }

body_item :
| PLACEHOLDER { DPlaceholder }
| LANGLE id=IDENT RANGLE { DId id }
| d=decl { DNested d }




%%
