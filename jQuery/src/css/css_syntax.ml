type atomic = TSel of string | USel
and spec = | SpId of string | SpClass of string
           | SpAttrib of string * (oper * string) option | SpPseudo of string
and oper = AOEquals | AOStartsWith | AOEndsWith | AOPrefixedWith | AOContainsClass | AOSubstring
type simple = atomic * spec list
type combinator = Desc | Kid | Sib | Adj
type regsel = (combinator * simple) list
