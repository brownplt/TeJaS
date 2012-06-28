open JQuery_types
open JQuery_syntax
open TypImpl


type attribs = string list * string list * string list
type declComp = Decl of string * string option * string * attribs * dcContent list
and dcContent =
  | DPlaceholder
  | DNested of declComp
  | DId of string
and declSyntax = declComp list

type lsid = LSId of string

module StringMap = Map.Make (String)

module LSIdOrderedType = struct
  type t = lsid
  let compare = Pervasives.compare
end

module LSIdMap = Map.Make (LSIdOrderedType)

module LSIdMapExt = MapExt.Make (LSIdOrderedType) (LSIdMap)

type preClauseMap = typ list LSIdMap.t

type clauseMap = multiplicity LSIdMap.t

type backformMap = lsid list StringMap.t

module StringMapExt = MapExt.Make (String) (StringMap)

type backformEnv = BackformEnv of backformMap * backformMap * backformMap
                 (* child, par, prev, next *)
type clauseEnv = ClauseEnv of clauseMap * clauseMap * clauseMap * clauseMap
type preClauseEnv = PreClauseEnv of preClauseMap * preClauseMap * preClauseMap * preClauseMap
type preStructureEnv = backformEnv * preClauseEnv
type structureEnv = backformEnv * clauseEnv



