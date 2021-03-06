%{

open Prelude
open JQuery_syntax
module W = Typedjs_writtyp.WritTyp

let concat (r1, o1, i1) (r2, o2, i2) = (r1 @ r2, o1 @ o2, i1 @ i2)

let rec remove_this op = match op with
  | W.Arrow (_, aa, v, r) -> W.Arrow (None, aa, v, r)
  | W.Inter (t1, t2) -> W.Inter (remove_this t1, remove_this t2)
  | W.Forall (x, s, t) -> W.Forall (x, s, remove_this t)
  | W.Ref (W.Object (W.Present(_, t)::fields)) -> remove_this t
  | W.With(t, f) -> W.With(remove_this t, f)
  | _ -> failwith "remove_this : illegal argument"

let wrapArrow isRef arrTyp =
  let o = W.Object ([W.Present(Pat.singleton "-*- code -*-", arrTyp);
                     W.Present(Pat.singleton "__proto__", W.TId "Object"); (* ADDING THIS CAUSES AN ERROR "Object is unbound" *)
                     W.Present(Pat.singleton "prototype", W.TId "Ext");
                     W.Star(Some (W.TId "Ext"))]) in
  if isRef then W.Ref o else W.Source o

let matchArrow t = match t with
  | W.Ref(W.Object([W.Present(code, t);
                    W.Present(proto, W.TId "Object");
                    W.Present(prototypePat, W.TId "Ext");
                    W.Star(Some (W.TId "Ext"))])) -> Some (t, true)
  | W.Source(W.Object([W.Present(code, t);
                       W.Present(proto, W.TId "Object");
                       W.Present(prototypePat, W.TId "Ext");
                       W.Star(Some (W.TId "Ext"))])) -> Some (t, false)
  | _ -> None

let makeReadonly t = match t with W.Ref t -> W.Source t | _ -> t

let rec pushForallFunction typ = match typ with
  | W.Forall (var, bound, t) -> begin
    match (matchArrow t) with
    | Some (W.Arrow _ as arrTyp, isRef)
    | Some (W.Forall _ as arrTyp, isRef) ->
      wrapArrow isRef (W.Forall(var, bound, arrTyp))
    | Some _
    | None -> Printf.eprintf "Found a forall that couldn't be pushed %s\n" (W.string_of_typ typ); typ
  end
  | W.With(t, f) -> W.With(pushForallFunction t, f)
  | _ -> typ

let rec pushIntersectFunction typ = match typ with
  | W.Inter(t1, t2) -> begin match (matchArrow t1, matchArrow t2) with
    | Some (t1, isRef1), Some (t2, isRef2) -> 
      wrapArrow (isRef1 && isRef2) (W.Inter (t1, t2))
    | _, _ -> Printf.eprintf "Didn't get two function objects to pushIntersectFunction: \n%s\nand\n%s\n"
      (W.string_of_typ t1) (W.string_of_typ t2); typ
  end
  | _ -> typ
%}

%token <string> ID TID STRING REGEX PRIM DOCSTRING
%token ARROW LPAREN RPAREN ANY STAR COLON EOF UNION STR AND 
       MULT ZERO ONE ZEROONE ZEROPLUS ONEPLUS SUM
       BOOL LBRACE RBRACE COMMA VAL LBRACK RBRACK DOT OPERATOR SEMI
       UPCAST DOWNCAST FORALL LTCOLON IS LANGLE RANGLE
       CHEAT REC INTERSECTION UNDERSCORE BAD WITH THIS
       HASHBRACE HASHPAREN EQUALS TYPE QUES BANG TYPREC TYPLAMBDA THICKARROW
       COLONCOLON CARET LLBRACE RRBRACE REF PRIMITIVE DOTS
       CONSTRUCTOR PROTOTYPE INSTANCE IDS CLASSES OPTIONAL

%right UNION INTERSECTION THICKARROW REF
%left LANGLE

%start typ_ann
%start env


%type <Typedjs_writtyp.WritTyp.annotation> typ_ann
%type <Typedjs_writtyp.WritTyp.env_decl list> env

%%

kind :
  | STAR { W.KStar }
  | LPAREN kind RPAREN { $2 }
  | MULT LANGLE kind RANGLE { W.KMult $3 }
  | LPAREN k1=kind COMMA ks=separated_nonempty_list(COMMA, kind) RPAREN THICKARROW ret=kind 
    { W.KArrow (k1 :: ks, ret) }
  | kind THICKARROW kind { W.KArrow ([$1], $3) }

args
  :  { ([], None) }
  | arg_typ { ([$1], None) }
  | arg_typ DOTS { ([], Some $1) }
  | arg_typ STAR args { let (args, var) = $3 in (($1 :: args), var) }

pat :
  | REGEX { (Pat.parse $startpos $1, true) }
  | any_id { (Pat.singleton $1, false) }
  | STRING { (Pat.singleton $1, false) }

field :
  | pat COLON QUES typ { W.Maybe (fst2 $1, $4) }
  | pat COLON BANG typ { W.Present (fst2 $1, $4) }
  | pat COLON typ
      { let (pat, is_regex) = $1 in
  if is_regex then
          W.Maybe (pat, $3)
  else
         W.Present (pat, $3) }
  | pat COLON CARET typ { W.Inherited (fst2 $1, $4) }
  | pat COLON UNDERSCORE { W.Absent (fst2 $1) }
  | pat COLON BAD { W.Skull (fst2 $1) }
  | STAR COLON typ { W.Star (Some $3) }
  | STAR COLON UNDERSCORE { W.Star None }

fields
  : { [] }
  | field { [$1] }
  | field COMMA fields { $1 :: $3 }
  | COMMA { [] }

obj_ref_typ:
  | LBRACE fields RBRACE { W.Ref (W.Object $2) }
  | HASHBRACE fields RBRACE { W.Source (W.Object $2) }
  | LBRACE typ WITH fields RBRACE { W.With($2, $4) }


arg_typ
  : ANY { W.Top }
  | PRIM { W.Prim $1 }
  | STR { W.Str }
  | BOOL { W.Bool }
  | REGEX { W.Pat (Pat.parse $startpos $1) }
  | arg_typ UNION arg_typ { W.Union ($1, $3) }
  | arg_typ INTERSECTION arg_typ { pushIntersectFunction (W.Inter ($1, $3)) }
  | LPAREN typ RPAREN { $2 }
  | HASHPAREN typ RPAREN { makeReadonly $2 }
  | LLBRACE fields RRBRACE { W.Object $2 }
  | obj_ref_typ { $1 }
  | TID { W.TId $1 }
  | ID { W.Syn $1 }
  | REF arg_typ { W.Ref $2 } 
  | arg_typ LANGLE sigma_list RANGLE { W.App ($1, $3) }

sigma
  : typ { W.Typ $1 }
  | mult { W.Mult $1 }

sigma_list :
  |  { [] }
  | sigma { [$1] }
  | sigma COMMA sigma_list { $1 :: $3 }


typ :
  | arg_typ { $1 }
  | args ARROW typ { let (args, var) = $1 in wrapArrow true (W.Arrow (Some W.Top, args, var, $3)) }
  | LBRACK typ RBRACK args ARROW typ { let (args, var) = $4 in wrapArrow true (W.Arrow (Some $2, args, var, $6)) }
  | LBRACK THIS LPAREN typ RPAREN RBRACK args ARROW typ 
      { let (args, var) = $7 in wrapArrow true (W.Arrow (Some (W.This $4), args, var, $9)) }
  | LBRACK RBRACK args ARROW typ { let (args, var) = $3 in wrapArrow true (W.Arrow (None, args, var, $5)) }
  | args THICKARROW typ { let (args, var) = $1 in W.Arrow (Some W.Top, args, var, $3) }
  | LBRACK typ RBRACK args THICKARROW typ { let (args, var) = $4 in W.Arrow (Some $2, args, var, $6) }
  | LBRACK THIS LPAREN typ RPAREN RBRACK args THICKARROW typ 
      { let (args, var) = $7 in W.Arrow (Some (W.This $4), args, var, $9) }
  | LBRACK RBRACK args THICKARROW typ { let (args, var) = $3 in W.Arrow (None, args, var, $5) }
  | FORALL ID LTCOLON sigma DOT typ { pushForallFunction (W.Forall ($2, $4, $6)) }
  | FORALL ID DOT typ { pushForallFunction (W.Forall ($2, W.Typ W.Top, $4)) }
  | FORALL ID LTCOLON sigma COLON typ {  (W.Forall ($2, $4, $6)) } (* Allow for not pushing forall inward *)
  | FORALL ID COLON typ {  (W.Forall ($2, W.Typ W.Top, $4)) }
  | REC ID DOT typ { W.Rec ($2, $4) }
  | TYPLAMBDA args=separated_nonempty_list(COMMA, id_kind) DOT typ=typ
    { W.Lambda (args, typ) }
  | TYPREC ID COLONCOLON kind DOT typ { W.Fix ($2, $4, $6) }

mult :
  | ZERO LANGLE mult RANGLE { W.Zero $3 }
  | ONE LANGLE mult RANGLE { W.One $3 }
  | ZEROONE LANGLE mult RANGLE { W.ZeroOne $3 }
  | ZEROPLUS LANGLE mult RANGLE { W.ZeroPlus $3 }
  | ONEPLUS LANGLE mult RANGLE { W.OnePlus $3 }
  | SUM LANGLE mult COMMA mult RANGLE { W.Sum ($3, $5) }
  | ZERO LANGLE typ RANGLE { W.Zero (W.Plain $3) }
  | ONE LANGLE typ RANGLE { W.One (W.Plain $3) }
  | ZEROONE LANGLE typ RANGLE { W.ZeroOne (W.Plain $3) }
  | ZEROPLUS LANGLE typ RANGLE { W.ZeroPlus (W.Plain $3) }
  | ONEPLUS LANGLE typ RANGLE { W.OnePlus (W.Plain $3) }
  | SUM LANGLE typ COMMA mult RANGLE { W.Sum (W.Plain $3, $5) }
  | SUM LANGLE mult COMMA typ RANGLE { W.Sum ($3, W.Plain $5) }
  | SUM LANGLE typ COMMA typ RANGLE { W.Sum (W.Plain $3, W.Plain $5) }

id_kind : ID COLONCOLON kind { ($1, $3) }

typ_app : LBRACK t=typ RBRACK { t }

annotation :
  | typ { W.ATyp $1 }
  | CHEAT typ { W.ACheat $2 }
  | UPCAST typ { W.AUpcast $2 }
  | DOWNCAST typ { W.ADowncast $2 }
  | FORALL ID LTCOLON typ { W.ATypAbs ($2, $4) }
  | FORALL ID { W.ATypAbs ($2, W.Top) }
  | LBRACK typ RBRACK { W.ATypApp [$2] }
  | ID BANG typs=nonempty_list(typ_app) { W.ATypApp typs }
  | IS typ { W.AAssertTyp $2 }

typ_ann :
  | annotation EOF { $1 }

any_id :
  | ID { $1 }
  | PRIM { $1 }
  | IDS { "ids" }
  | CLASSES { "classes" }
  | OPTIONAL { "optional" }
  | MULT { "M" }
  | SUM { "Sum "}
  | STR { "Str" }
  | BOOL { "Bool" }
  | PROTOTYPE { "prototype" }
  | CONSTRUCTOR { "constructor" }
  | INSTANCE { "instance" }


id_list :
  | { [] }
  | ID { [$1] }
  | ID COMMA id_list { $1 :: $3 }

env_decl :
  | TYPE CONSTRUCTOR c_id=any_id EQUALS c_typ=typ
      AND PROTOTYPE p_id=any_id EQUALS p_typ=obj_ref_typ
      AND INSTANCE i_id=any_id EQUALS i_typ=obj_ref_typ
    { W.ObjectTrio (Pos.real ($startpos, $endpos), (c_id, c_typ), (p_id, p_typ), (i_id, i_typ)) }
  | TYPE any_id LANGLE id_list RANGLE EQUALS typ 
      { W.EnvType (Pos.real ($startpos, $endpos), $2,
     W.Lambda (List.map (fun x -> (x, W.KStar)) $4, $7)) }
  | TYPE any_id EQUALS typ { W.EnvType (Pos.real ($startpos, $endpos), $2, $4) }
  | VAL ID COLON typ { W.EnvBind (Pos.real ($startpos, $endpos), $2, $4) }
  | ID COLON typ { W.EnvBind (Pos.real ($startpos, $endpos), $1, W.Ref $3) }
  | OPERATOR STRING COLON typ 
      { W.EnvBind (Pos.real ($startpos, $endpos), $2, remove_this $4) }
  | PRIMITIVE PRIM { W.EnvPrim (Pos.real ($startpos, $endpos), $2) }
  | decl { W.Decl (Pos.real ($startpos, $endpos), $1) }

decl :
  | LPAREN declname=ID COLON desc=DOCSTRING? tyname=ID attribs=attribs body=list(body_item) RPAREN
    { (declname, desc, tyname, attribs, body) }

attribs :
| attribs=nonempty_list(attrib) { List.fold_left concat ([], [], []) attribs }

attrib :
| CLASSES EQUALS LBRACK cs=separated_nonempty_list(COMMA, ID) RBRACK { (cs, [], []) }
| OPTIONAL CLASSES EQUALS LBRACK cs=separated_nonempty_list(COMMA, ID) RBRACK { ([], cs, []) }
| IDS EQUALS LBRACK ids=separated_nonempty_list(COMMA, ID) RBRACK { ([], [], ids) }

body_item :
| DOTS { W.DPlaceholder }
| LANGLE id=ID RANGLE { W.DId id }
| d=decl { W.DNested d }



rec_env_decl : 
  | env_decl { $1 }
  | REC recs=separated_nonempty_list(AND, env_decl) { W.RecBind(recs) }

env_decls
  : { [] }
  | rec_env_decl SEMI? env_decls { $1 :: $3 }

env
  : env_decls EOF { $1 }

%%
