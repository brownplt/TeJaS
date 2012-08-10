open Prelude

type atomic = TSel of string | USel
and spec = | SpId of string | SpClass of string
           | SpSpecClass of string * bool
           | SpAttrib of string * (oper * string) option | SpPseudo of string
and oper = AOEquals | AOStartsWith | AOEndsWith | AOPrefixedWith | AOContainsClass | AOSubstring
type simple = atomic * spec list
type combinator = Desc | Kid | Sib | Adj
type regsel = (combinator * simple) list

let compare_comb c1 c2 = match c1, c2 with
  | Adj, Adj
  | Sib, Sib
  | Kid, Kid
  | Desc, Desc -> 0
  | Adj, _ -> -1
  | Sib, Adj -> 1
  | Sib, _ -> -1
  | Kid, Desc -> -1
  | Kid, _ -> 1
  | Desc, _ -> 1
let compare_atomic a1 a2 = match a1, a2 with
  | USel, USel -> 0
  | TSel _, USel -> 1
  | USel, TSel _ -> -1
  | TSel a1, TSel a2 -> String.compare a1 a2
let compare_oper o1 o2 = match o1, o2 with
  | AOEquals, AOEquals
  | AOEquals, _ -> -1
  | AOStartsWith, AOEquals -> 1
  | AOStartsWith, AOStartsWith -> 0
  | AOStartsWith, _ -> -1
  | AOEndsWith, AOEquals
  | AOEndsWith, AOStartsWith -> -1
  | AOEndsWith, AOEndsWith -> 0
  | AOEndsWith, _ -> 1
  | AOPrefixedWith, AOEquals
  | AOPrefixedWith, AOStartsWith
  | AOPrefixedWith, AOEndsWith -> -1
  | AOPrefixedWith, AOPrefixedWith -> 0
  | AOPrefixedWith, _ -> 1
  | AOContainsClass, AOSubstring -> 1
  | AOContainsClass, AOContainsClass -> 0
  | AOContainsClass, _ -> -1
  | AOSubstring, AOSubstring -> 0
  | AOSubstring, _ -> 1
let compare_spec s1 s2 = match s1, s2 with
  | SpId s1, SpId s2
  | SpClass s1, SpClass s2
  | SpPseudo s1, SpPseudo s2 -> String.compare s1 s2
  | SpSpecClass (_, true), SpSpecClass (_, false) -> -1
  | SpSpecClass (_, false), SpSpecClass (_, true) -> 1
  | SpSpecClass (s1, _), SpSpecClass (s2, _) -> String.compare s1 s2
  | SpAttrib (_, None), SpAttrib (_, Some _) -> -1
  | SpAttrib (_, Some _), SpAttrib (_, None) -> 1
  | SpAttrib (s1, None), SpAttrib (s2, None) -> String.compare s1 s2
  | SpAttrib (s11, Some (o1, s12)), SpAttrib (s21, Some (o2, s22)) ->
    let c = String.compare s11 s21 in
    if c != 0 then c else
      let o = compare_oper o1 o2 in
      if o != 0 then o else String.compare s12 s22
  | SpId _, _ -> -1
  | SpClass _, SpId _ -> 1
  | SpClass _, _ -> -1
  | SpSpecClass _, SpId _
  | SpSpecClass _, SpClass _ -> -1
  | SpSpecClass _, _ -> 1
  | SpAttrib _, SpPseudo _ -> 1
  | SpAttrib _, _ -> -1
  | SpPseudo _, _ -> 1  
let compare_simple (s1a, s1s) (s2a, s2s) =
  let a = compare_atomic s1a s2a in
  if a != 0 then a
  else 
    let rec helper s1s s2s = match s1s, s2s with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | s1::s1s, s2::s2s ->
      let s = compare_spec s1 s2 in
      if s != 0 then s else helper s1s s2s
    in helper s1s s2s
let rec compare_regsel r1 r2 = match r1, r2 with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | (r1c, r1s)::more_r1, (r2c, r2s)::more_r2 ->
    let c = compare_comb r1c r2c in
    if c = 0 then 
      let s = compare_simple r1s r2s in
      if s = 0 then compare_regsel more_r1 more_r2 else s
    else c


module Simple = struct
  type t = simple
  let compare = compare_simple
end
module Spec = struct
  type t = spec
  let compare = compare_spec
end

module SimpleSelSet = Set.Make (Simple)
module SimpleSelSetExt = SetExt.Make(SimpleSelSet)
module SpecSet = Set.Make (Spec)
module SpecSetExt = SetExt.Make(SpecSet)

