type attribs = string list * string list * string list
type declComp = Decl of string * string option * string * attribs * dcContent list
and dcContent =
  | DPlaceholder
  | DNested of declComp
  | DId of string
and declSyntax = declComp list



(* type classes = string list *)
(* type decl = typ * classes * classes * string * content list *)
(* type content = Placeholder | Id of id *)
(* type declEnv = decl IdMap.t *)

(* type clauseEnv = multiplicity IdMap.t *)

(* type typeEnv = clauseEnv * clauseEnv * clauseEnv * clauseEnv *)

(* type dom = typ * sel *)
(* type selmap = Sel -> id *)
