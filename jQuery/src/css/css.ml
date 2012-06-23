open Prelude
open Sig
open SetExt

module type CSS = sig
  include  SET
  type combinator = Desc | Kid | Sib | Adj
  val concat_selectors : t -> combinator -> t -> t
  val p_css : t -> FormatExt.printer
end

module Map2Sets (Src : Set.S) (Dst : Set.S) = struct
  let map (f : Src.elt -> Dst.elt) (s : Src.t) : Dst.t =
    Src.fold (fun e acc -> Dst.add (f e) acc) s Dst.empty
end
module Cross2Sets (Src1 : Set.S) (Src2 : Set.S) (Dst : Set.S) = struct
  let cross (f : Src1.elt -> Src2.elt -> Dst.elt) (s1 : Src1.t) (s2 : Src2.t) : Dst.t =
    Src1.fold (fun elt1 acc ->
      Src2.fold (fun elt2 acc ->
        Dst.add (f elt1 elt2) acc) s2 acc) s1 Dst.empty
end

module RealCSS = struct
  module R = Sb_strPat

  type atomic = TSel of string | USel
  and spec = | SpId of string | SpClass of string
             | SpAttrib of string * (oper * string) option | SpPseudo of string
  and oper = AOEquals | AOStartsWith | AOEndsWith | AOPrefixedWith | AOContainsClass | AOSubstring
  and simple = atomic * spec list
  and adj = A of adj * simple | AS of simple
  and sib = S of sib * adj | SA of adj
  and kid = K of kid * sib | KS of sib
  and desc = D of desc * kid | DK of kid
  and sel = desc
  type combinator = Desc | Kid | Sib | Adj

  type regsel = ((combinator * simple) list)

  let rec simple2regsel c s = [c, s]
  and adj2regsel c a = match a with
    | AS s -> simple2regsel c s
    | A(a, s) -> match adj2regsel c a, simple2regsel c s with
      | ra, (_,s)::tl -> ra @ (Adj, s) :: tl
      | _ -> failwith "impossible1"
  and sib2regsel c s = match s with
    | SA a -> adj2regsel c a
    | S(s, a) -> match sib2regsel c s, adj2regsel c a with
      | rs, (_, a)::tl -> rs @ (Sib, a) :: tl
      | _ -> failwith "impossible2"
  and kid2regsel c k = match k with
    | KS s -> sib2regsel c s
    | K(k, s) -> match kid2regsel c k, sib2regsel c s with
      | rk, (_,s)::tl -> rk @ (Kid, s) :: tl
      | _ -> failwith "impossible3"
  and desc2regsel c d = match d with
    | DK k -> kid2regsel c k
    | D(d, k) -> match desc2regsel c d, kid2regsel c k with
      | rd, (_, k)::tl -> rd @ (Desc, k) :: tl
      | _ -> failwith "impossible4"
  let adj2regsel = adj2regsel Adj
  let sib2regsel = sib2regsel Sib
  let kid2regsel = kid2regsel Kid
  let desc2regsel = desc2regsel Desc

  let (regsel2adj, regsel2sib, regsel2kid, regsel2desc) =
    let regsel2adjs rs =
      let rs' = List.map (fun (c, s) -> (c, AS s)) rs in
      let rec s2a al = match al with
        | [] -> []
        | (c, a1)::(Adj, (AS s2))::tl -> s2a ((c, A(a1, s2))::tl)
        | (c, a1)::tl -> (c, a1)::s2a tl in
      s2a rs' in
    let adjs2sibs adjs =
      let adjs' = List.map (fun (c, a) -> (c, SA a)) adjs in
      let rec a2sib sl = match sl with
        | [] -> []
        | (c, s1)::(Sib, (SA a2))::tl -> a2sib ((c, S(s1, a2))::tl)
        | (c, s1)::tl -> (c, s1)::a2sib tl in
      a2sib adjs' in
    let sibs2kids sibs =
      let sibs' = List.map (fun (c, s) -> (c, KS s)) sibs in
      let rec s2k kl = match kl with
        | [] -> []
        | (c, k1)::(Kid, (KS s2))::tl -> s2k ((c, K(k1, s2))::tl)
        | (c, k1)::tl -> (c, k1)::s2k tl in
      s2k sibs' in
    let kids2descs kids =
      let kids' = List.map (fun (c, k) -> (c, DK k)) kids in
      let rec k2d dl = match dl with
        | [] -> []
        | (c, d1)::(Desc, (DK k2))::tl -> k2d ((c, D(d1, k2))::tl)
        | (c, d1)::tl -> (c, d1)::k2d tl in 
      k2d kids' in
    let regsel2desc rs =
      match (kids2descs (sibs2kids (adjs2sibs (regsel2adjs rs)))) with
      | [(Desc, d)] -> d
      | d -> failwith "impossible5" in
    let regsel2kid rs =
      match (sibs2kids (adjs2sibs (regsel2adjs rs))) with
      | [(Kid, k)] -> k
      | k -> failwith "impossible6" in
    let regsel2sib rs =
      match (adjs2sibs (regsel2adjs rs)) with
      | [(Sib, s)] -> s
      | s -> failwith "impossible7" in
    let regsel2adj rs =
      match (regsel2adjs rs) with
      | [(Adj, a)] -> a
      | a -> failwith "impossible8" in

    (regsel2adj, regsel2sib, regsel2kid, regsel2desc)


  module AsRegex = struct
    let concat r1 r2 = R.concat r1 r2
    let concats rs = match rs with [] -> R.empty | r::rs -> List.fold_left concat r rs
    let alt r1 r2 = R.union r1 r2
    let alts rs = match rs with [] -> R.empty | r::rs -> List.fold_left alt r rs
    let option r = alt r R.empty
    let surround s1 s2 r = concats [R.singleton s1; r; R.singleton s2]
    let ident = concat (R.range [('a', 'z'); ('A', 'Z')])
      (R.star (R.range [('a', 'z'); ('A', 'Z'); ('0', '9'); ('_', '_')]))
    (* let ident = R.range [('a', 'z')] *) (* debugging only *)
    let noDelims = R.negate (R.range (List.map (fun r -> (r, r)) ['['; '{'; '}'; ']'; '"']))
    let comb2regex c = 
      let comb = match c with
      | Desc -> alt (R.singleton ">") (R.singleton "_")
      | Kid -> R.singleton ">"
      | Sib -> alt (R.singleton "+") (R.singleton "~")
      | Adj -> R.singleton "+" in
      surround "{{" "}}" comb
    let simple2regex (a, ss) = 
      let ra = match a with
        | TSel s -> R.singleton s
        | USel -> option ident in
      let rss = List.map (fun s -> match s with
        | SpId s -> concat (R.singleton "#") (R.singleton s)
        | SpClass s -> concat (R.singleton ".") (R.singleton s)
        | SpPseudo s -> concat (R.singleton ":") (R.singleton s)
        | SpAttrib (a, None) -> surround "[" "]" (R.singleton a)
        | SpAttrib (a, Some (o, v)) -> surround "[" "]" 
          (concats [R.singleton a; R.singleton "="; surround "\"" "\"" (match o with
          | AOEquals -> R.singleton v
          | AOStartsWith -> concat (R.singleton v) (R.star noDelims)
          | AOEndsWith -> concat (R.star noDelims) (R.singleton v)
          | AOPrefixedWith -> concats [R.singleton v; option (R.singleton "-"); R.star noDelims]
          | AOContainsClass -> concats [option (concat (R.star noDelims) (R.singleton " "));
                                        R.singleton v;
                                        option (concat (R.star noDelims) (R.singleton " "))]
          | AOSubstring -> concats [R.star noDelims; R.singleton v; R.star noDelims]
           )])
      ) ss in
      let fallback = (R.star (R.negate (R.singleton "}"))) in
      surround "{" "}" (concats (ra::rss@[fallback]))
    let rec adj2regex a = match a with
      | AS s -> simple2regex s
      | A(a, s) -> concats [adj2regex a; comb2regex Adj; simple2regex s]
    let rec sib2regex s = match s with
      | SA a -> concat (R.star (concat (adj2regex (AS (USel, []))) (comb2regex Sib))) (adj2regex a)
      | S(s, a) -> concats [sib2regex s;
                            R.star (concat (comb2regex Sib) (adj2regex (AS (USel, []))));
                            comb2regex Sib; adj2regex a]
    let rec kid2regex k = match k with
      | KS s -> sib2regex s
      | K(k, s) -> concats [kid2regex k; comb2regex Kid; sib2regex s]
    let rec desc2regex d = match d with
      | DK k -> concat (R.star (concat (kid2regex (KS (SA (AS (USel, []))))) (comb2regex Desc))) (kid2regex k)
      | D(d, k) -> concats [desc2regex d;
                            R.star (concat (comb2regex Desc) (kid2regex (KS (SA (AS (USel, []))))));
                            comb2regex Desc; kid2regex k]

    let sel2regex s = desc2regex s
  end


  module SelOrdered = struct
    type t = sel
    let compare = compare
  end
  module KidOrdered = struct
    type t = kid
    let compare = compare
  end
  module SibOrdered = struct
    type t = sib
    let compare = compare
  end
  module AdjOrdered = struct
    type t = adj
    let compare = compare
  end
  module SimpleOrdered = struct
    type t = simple
    let compare = compare
  end
  module SelSet = Set.Make (SelOrdered)
  module KidSet = Set.Make (KidOrdered)
  module SibSet = Set.Make (SibOrdered)
  module AdjSet = Set.Make (AdjOrdered)
  module SimpleSet = Set.Make (SimpleOrdered)
  module SelSetExt = SetExt.Make (SelSet)
  module KidSetExt = SetExt.Make (KidSet)
  module SibSetExt = SetExt.Make (SibSet)
  module AdjSetExt = SetExt.Make (AdjSet)
  module SimpleSetExt = SetExt.Make (SimpleSet)

  let concat_selectors_gen toRegsel1 fromRegsel cross s1 comb s2 =
    let helper d1 comb d2 =
      let rd1 = toRegsel1 d1 in
      let rd2 = toRegsel1 d2 in
      fromRegsel (rd1 @ (comb, (snd (List.hd rd2))) :: (List.tl rd2)) in
    cross (fun s1 s2 -> helper s1 comb s2) s1 s2


  module type UniformSelector = sig
    type sel
    type part
    val comb : combinator
    module SetOfSel : Set.S with type elt = sel
    module SetOfPart : Set.S with type elt = part
    val toParts : sel -> part list
    val fromParts : part list -> sel
    val concat : combinator -> SetOfSel.t -> SetOfSel.t -> SetOfSel.t
    val lift : SetOfPart.t -> SetOfSel.t
  end

  module AdjSelector = struct
    type sel = adj
    type part = simple
    type t = sel
    let compare = compare
    let comb = Adj
    module SetOfSel = AdjSet
    module SetOfPart = SimpleSet
    let toParts a =
      let rec helper a acc = match a with
        | AS s -> s :: acc
        | A (a, s) -> helper a (s :: acc) in
      helper a []
    let fromParts slist = match slist with
      | [] -> failwith "impossible9"
      | s::tl -> List.fold_left (fun a s -> A (a, s)) (AS s) tl
    let concat comb s1 s2 = 
      let module AdjAdjCross = Cross2Sets (AdjSet) (AdjSet) (AdjSet) in
      concat_selectors_gen adj2regsel regsel2adj AdjAdjCross.cross s1 comb s2
    let lift sims = AdjSetExt.from_list (List.map (fun s -> AS s) (SimpleSetExt.to_list sims))
  end
  module SibSelector = struct
    type sel = sib
    type part = adj
    type t = sel
    let compare = compare
    let comb = Sib
    module SetOfSel = SibSet
    module SetOfPart = AdjSet
    let toParts s =
      let rec helper s acc = match s with
        | SA a -> a :: acc
        | S (s, a) -> helper s (a :: acc) in
      helper s []
    let fromParts alist = match alist with
      | [] -> failwith "impossible10"
      | a::tl -> List.fold_left (fun s a -> S (s, a)) (SA a) tl
    let concat comb s1 s2 = 
      let module SibSibCross = Cross2Sets (SibSet) (SibSet) (SibSet) in
      concat_selectors_gen sib2regsel regsel2sib SibSibCross.cross s1 comb s2
    let lift adjs = SibSetExt.from_list (List.map (fun s -> SA s) (AdjSetExt.to_list adjs))
  end
  module KidSelector = struct
    type sel = kid
    type part = sib
    type t = sel
    let compare = compare
    let comb = Kid
    module SetOfSel = KidSet
    module SetOfPart = SibSet
    let toParts k =       
      let rec helper k acc = match k with
        | KS s -> s :: acc
        | K (k, s) -> helper k (s :: acc) in
      helper k []
    let fromParts slist = match slist with
      | [] -> failwith "impossible11"
      | s::tl -> List.fold_left (fun k s -> K (k, s)) (KS s) tl
    let concat comb s1 s2 = 
      let module KidKidCross = Cross2Sets (KidSet) (KidSet) (KidSet) in
      concat_selectors_gen kid2regsel regsel2kid KidKidCross.cross s1 comb s2
    let lift sibs = KidSetExt.from_list (List.map (fun s -> KS s) (SibSetExt.to_list sibs))
  end
  module DescSelector = struct
    type sel = desc
    type part = kid
    type t = sel
    let compare = compare
    let comb = Desc
    module SetOfSel = SelSet
    module SetOfPart = KidSet
    let toParts d =
      let rec helper d acc = match d with
        | DK k -> k :: acc
        | D (d, k) -> helper d (k :: acc) in
      helper d []
    let fromParts klist = match klist with
      | [] -> failwith "impossible12"
      | k::tl -> List.fold_left (fun d k -> D (d, k)) (DK k) tl
    let concat comb s1 s2 = 
      let module SelSelCross = Cross2Sets (SelSet) (SelSet) (SelSet) in
      concat_selectors_gen desc2regsel regsel2desc SelSelCross.cross s1 comb s2
    let lift kids = SelSetExt.from_list (List.map (fun s -> DK s) (KidSetExt.to_list kids))
  end



  type t = SelSet.t
  let parse _ _ = SelSet.empty
  let empty = SelSet.empty
  let all = SelSet.singleton (DK (KS (SA (AS (USel, [])))))
  let concat_selectors s1 c s2 = DescSelector.concat c s1 s2


  module Pretty = struct
    open FormatExt
    let pretty_list p_item p_comb lst =
      (add_sep_between p_comb (List.map p_item lst), List.length lst > 1)
    let rec pretty_atomic a =
      match a with 
      | USel -> text "*"
      | TSel t -> text t
    and pretty_spec s = List.map (fun s -> match s with
      | SpId s -> squish [text "#"; text s]
      | SpClass s -> squish [text "."; text s]
      | SpAttrib (s, None) -> brackets [text s]
      | SpAttrib (s, Some (op, v)) -> begin match op with
        | AOEquals -> brackets [squish [text s; text "="; string v]]
        | AOStartsWith -> brackets [squish [text s; text "^="; string v]]
        | AOEndsWith -> brackets [squish [text s; text "$="; string v]]
        | AOPrefixedWith -> brackets [squish [text s; text "|="; string v]]
        | AOContainsClass -> brackets [squish [text s; text "~="; string v]]
        | AOSubstring -> brackets [squish [text s; text "*="; string v]]
      end
      | SpPseudo s -> squish [text ":"; text s]) s
    and pretty_simple (a, s) = squish (pretty_atomic a :: pretty_spec s)
    and parensOrHOV (lst, b) =
      let parens = enclose 1 "" empty (text "(") (text ")") in
      if b then parens lst else horzOrVert lst
    and pretty_adj a : printer = 
      parensOrHOV (pretty_list pretty_simple (text " +") (AdjSelector.toParts a))
    and pretty_sib s = 
      parensOrHOV (pretty_list pretty_adj (text " ~") (SibSelector.toParts s))
    and pretty_kid k = 
      parensOrHOV (pretty_list pretty_sib (text " >") (KidSelector.toParts k))
    and pretty_desc d = 
      horzOrVert (fst (pretty_list pretty_kid empty (DescSelector.toParts d)))
    let pretty_sel = pretty_desc
    let pretty_regsel (rs : ((combinator * simple) list)) =
      match rs with
      | [] -> failwith "impossible13"
      | (c, s)::css ->
      let parens = enclose 1 "" empty (text "(") (text ")") in
      horzOrVert (List.fold_left 
                     (fun p (c, s) -> 
                       [squish [parens p; 
                                text (match c with
                                | Adj -> " +" | Sib -> " ~" 
                                | Kid -> " >" | Desc -> "")];
                        pretty_simple s])
                     [pretty_simple s] css)
  end





  module Specificity = struct
    let startswith haystack needle = String.length needle <= String.length haystack && String.sub haystack 0 (String.length needle) = needle
    let endswith haystack needle = String.length needle <= String.length haystack && String.sub haystack (String.length haystack - String.length needle) (String.length needle) = needle
    let contains haystack needle =
      let re = Str.regexp_string needle
      in try ignore (Str.search_forward re haystack 0); true
        with Not_found -> false
    let is_morespecific_spec s1 s2 v1 v2=
      match s1, s2 with
      | AOEquals, AOEquals -> v1 = v2
      | AOEquals, AOStartsWith -> startswith v1 v2
      | AOEquals, AOPrefixedWith -> startswith (v1 ^ "-") v2
      | AOEquals, AOEndsWith -> endswith v1 v2
      | AOEquals, AOContainsClass -> (not (String.contains v1 ' ')) && contains (" " ^ v1 ^ " ") (" " ^ v2 ^ " ")
      | AOEquals, AOSubstring -> contains v1 v2
      | AOStartsWith, AOEquals -> false
      | AOStartsWith, AOStartsWith -> startswith v1 v2
      | AOStartsWith, AOPrefixedWith -> startswith (v1 ^ "-") v2
      | AOStartsWith, AOEndsWith -> false
      | AOStartsWith, AOContainsClass -> (not (String.contains v1 ' ')) && startswith (v1 ^ " ") (v2 ^ " ")
      | AOStartsWith, AOSubstring -> contains v1 v2
      | AOEndsWith, AOEquals -> false
      | AOEndsWith, AOStartsWith -> false
      | AOEndsWith, AOPrefixedWith -> false
      | AOEndsWith, AOEndsWith -> endswith v1 v2
      | AOEndsWith, AOContainsClass -> (not (String.contains v1 ' ')) && endswith (" " ^ v1) (" " ^ v2)
      | AOEndsWith, AOSubstring -> contains v1 v2
      | AOPrefixedWith, AOEquals -> false
      | AOPrefixedWith, AOStartsWith -> startswith v1 v2
      | AOPrefixedWith, AOPrefixedWith -> startswith v1 v2
      | AOPrefixedWith, AOEndsWith -> false
      | AOPrefixedWith, AOContainsClass -> false
      | AOPrefixedWith, AOSubstring -> contains v1 v2
      | AOContainsClass, AOEquals
      | AOContainsClass, AOStartsWith
      | AOContainsClass, AOPrefixedWith
      | AOContainsClass, AOEndsWith -> false
      | AOContainsClass, AOContainsClass -> v1 = v2
      | AOContainsClass, AOSubstring -> contains v1 v2
      | AOSubstring, AOEquals
      | AOSubstring, AOStartsWith
      | AOSubstring, AOPrefixedWith
      | AOSubstring, AOEndsWith -> false
      | AOSubstring, AOContainsClass -> contains v1 v2
      | AOSubstring, AOSubstring -> contains v1 v2

    let is_morespecific_simple (a1a, a1s) (a2a, a2s) =
      (a1a = a2a || a2a = USel) &&
        List.for_all (fun s1 ->
          List.exists (fun s2 ->
            match s1, s2 with
            | SpId i1, SpId i2 -> i1 = i2
            | SpClass c1, SpClass c2 -> c1 = c2
            | SpPseudo p1, SpPseudo p2 -> p1 = p2
            | SpAttrib (s1name, s1prop), SpAttrib (s2name, s2prop) -> 
              s1name = s2name && (match s1prop, s2prop with
              | _, None -> true
              | None, Some _ -> false
              | Some (s1, v1), Some (s2, v2) -> is_morespecific_spec s1 s2 v1 v2)
            | _ -> false
          ) a2s) a1s

    let is_morespecific_sib s1 s2 = 
      let s1adjs = List.map (fun a -> (a, Sib)) (SibSelector.toParts s1) in
      let s1sims = List.map (fun (a, comb) -> 
        match List.map (fun s -> (s, Adj)) (AdjSelector.toParts a) with
        | [] -> []
        | (h,_)::tl -> (h,comb)::tl) s1adjs in
      let s1sims = List.rev (List.flatten s1sims) in
      let s2adjs = List.map (fun a -> (a, Sib)) (SibSelector.toParts s2) in
      let s2sims = List.map (fun (a, comb) -> 
        match List.map (fun s -> (s, Adj)) (AdjSelector.toParts a) with
        | [] -> []
        | (h,_)::tl -> (h,comb)::tl) s2adjs in
      let s2sims = List.rev (List.flatten s2sims) in
      let rec helper s1 s2 = match s1, s2 with
        | _, [] -> true (* s1 is still constrained; s2 isn't *)
        | [], _ -> false (* s2 still is constrained; s1 isn't *)
        | [(s1s, _)], [(s2s, _)] -> is_morespecific_simple s1s s2s
        | (s1s, Adj)::s1tl, (s2s, Adj)::s2tl ->
          is_morespecific_simple s1s s2s && helper s1tl s2tl
        | (s1s, Adj)::s1tl, (s2s, Sib)::s2tl ->
          is_morespecific_simple s1s s2s &&
            (helper s1tl s2tl || helper s1tl (((USel, []), Sib)::s2tl))
        | (s1s, Sib)::s1tl, (s2s, Sib)::s2tl ->
          is_morespecific_simple s1s s2s &&
            (helper s1tl s2tl || helper s1tl (((USel, []), Sib)::s2tl))
        | _ -> false in
      helper s1sims s2sims
    (* let rec is_morespecific_adj a1 a2 = match a1, a2 with *)
    (*   | A(_, a1s), AS a2s -> is_morespecific_simple a1s a2s *)
    (*   | AS _, A _ -> false *)
    (*   | AS a1s, AS a2s -> is_morespecific_simple a1s a2s *)
    (*   | A(a1a, a1s), A(a2a, a2s) -> is_morespecific_simple a1s a2s && is_morespecific_adj a1a a2a *)
    let is_morespecific_desc d1 d2 =
      let open Format in 
      let open FormatExt in
      let d1kids = List.map (fun a -> (a, Desc)) (DescSelector.toParts d1) in
      let d1sibs = List.map (fun (a, comb) -> 
        match List.map (fun s -> (s, Kid)) (KidSelector.toParts a) with
        | [] -> []
        | (h,_)::tl -> (h,comb)::tl) d1kids in
      let d1sibs = List.rev (List.flatten d1sibs) in
      let d2kids = List.map (fun a -> (a, Desc)) (DescSelector.toParts d2) in
      let d2sibs = List.map (fun (a, comb) -> 
        match List.map (fun s -> (s, Kid)) (KidSelector.toParts a) with
        | [] -> []
        | (h,_)::tl -> (h,comb)::tl) d2kids in
      let d2sibs = List.rev (List.flatten d2sibs) in
      let rec helper d1 d2 = match d1, d2 with
        | _, [] -> true (* d1 is still constrained; d2 isn't *)
        | [], _ -> false (* d2 still is constrained; d1 isn't *)
        | [(d1s, _)], [(d2s, _)] -> is_morespecific_sib d1s d2s
        | (d1s, Kid)::d1tl, (d2s, Kid)::d2tl ->
          vert [label "d1s(Kid): " [Pretty.pretty_sib d1s];
                label "d2s(Kid): " [Pretty.pretty_sib d2s]] std_formatter;
          print_newline ();
          let smatch = is_morespecific_sib d1s d2s in
          label "d1s <? d2s: " [bool smatch] std_formatter;
          print_newline ();
          smatch && helper d1tl d2tl
        | (d1s, Kid)::d1tl, (d2s, Desc)::d2tl ->
          vert [label "d1s(Kid ): " [Pretty.pretty_sib d1s];
                label "d2s(Desc): " [Pretty.pretty_sib d2s]] std_formatter;
          print_newline ();
          let smatch = is_morespecific_sib d1s d2s in
          label "d1s <? d2s: " [bool smatch] std_formatter;
          print_newline ();
          smatch && (helper d1tl d2tl || helper d1tl (((SA (AS (USel, []))), Desc)::d2tl))
        | (d1s, Desc)::d1tl, (d2s, Desc)::d2tl ->
          vert [label "d1s(Desc): " [Pretty.pretty_sib d1s];
                label "d2s(Desc): " [Pretty.pretty_sib d2s]] std_formatter;
          print_newline ();
          let smatch = is_morespecific_sib d1s d2s in
          label "d1s <? d2s: " [bool smatch] std_formatter;
          print_newline ();
          smatch && (helper d1tl d2tl || helper d1tl (((SA (AS (USel, []))), Desc)::d2tl))
        | _ -> false in
      helper d1sibs d2sibs

    let is_morespecific s1 s2 =
      let open Format in
      let open FormatExt in
      SelSet.for_all (fun s -> 
        label "Searching for match for: " [Pretty.pretty_sel s] std_formatter; print_newline ();
        SelSet.exists (fun t -> 
          label "Trying: " [Pretty.pretty_sel t] std_formatter; print_newline ();
          is_morespecific_desc s t) s2) s1
  end









  module type INTERLEAVINGS = functor (UnifSel : UniformSelector) -> sig
    val interleavings : (UnifSel.sel -> UnifSel.sel -> UnifSel.SetOfSel.t) ->
      UnifSel.sel -> UnifSel.sel -> UnifSel.SetOfSel.t
  end

  module Interleavings : INTERLEAVINGS = functor (UnifSel : UniformSelector) -> struct
    let rec interleavings (inter_single : UnifSel.sel -> UnifSel.sel -> UnifSel.SetOfSel.t)
        (s : UnifSel.sel) (t : UnifSel.sel) : UnifSel.SetOfSel.t =
      let interleavings = interleavings inter_single in
      let slist = UnifSel.toParts s in
      let tlist = UnifSel.toParts t in
      match slist, tlist with
      | [], _
      | _, [] -> failwith "impossible14"
      | [_], _
      | _, [_] -> inter_single s t
      | s1::s2N, t1::t2M ->
        let clause1 =
          let s1set = UnifSel.SetOfSel.singleton (UnifSel.fromParts [s1]) in
          let inter1 = interleavings (UnifSel.fromParts s2N) t in
          UnifSel.concat UnifSel.comb s1set inter1 in
        let clause2 =
          let t1set = UnifSel.SetOfSel.singleton (UnifSel.fromParts [t1]) in
          let inter2 = interleavings s (UnifSel.fromParts t2M) in
          UnifSel.concat UnifSel.comb t1set inter2 in
        let clause3 =
          let inter_lists ss ts =
            match ss, ts with
            | [], [] -> UnifSel.SetOfSel.empty
            | [], _ -> UnifSel.SetOfSel.singleton (UnifSel.fromParts ts)
            | _, [] -> UnifSel.SetOfSel.singleton (UnifSel.fromParts ss)
            | _ -> interleavings (UnifSel.fromParts ss) (UnifSel.fromParts ts) in
          List.fold_left UnifSel.SetOfSel.union UnifSel.SetOfSel.empty
            (List.map (fun i ->
              List.fold_left UnifSel.SetOfSel.union UnifSel.SetOfSel.empty
                (List.map (fun j ->
                  let (s1i, siN) = ListExt.split_at (i+1) slist in
                  let (t1j, tjM) = ListExt.split_at (j+1) tlist in
                  let inter_ij = inter_lists s1i t1j in
                  let inter_NM = inter_lists siN tjM in
                  UnifSel.concat UnifSel.comb inter_ij inter_NM
                 ) (iota (List.length tlist - 2)))
             ) (iota (List.length slist - 2))) in
        UnifSel.SetOfSel.union clause1 (UnifSel.SetOfSel.union clause2 clause3)
  end

  module Pairings (LooseSel : UniformSelector) 
    (TightSel : UniformSelector with type sel = LooseSel.part with type SetOfSel.t = LooseSel.SetOfPart.t) = struct
    let loose2lists (sel : LooseSel.sel) : (TightSel.part list * combinator list) =
      let tights = LooseSel.toParts sel in
      let parts = List.map TightSel.toParts tights in
      let combs = List.tl (List.flatten (List.map (fun parts ->
        let n = List.length parts - 1 in
        LooseSel.comb :: (List.map (fun _ -> TightSel.comb) (iota n))) parts)) in
      (List.flatten parts, combs)
    let split_at_each c lst =
      let rec helper lst acc =
        match lst, acc with
        | _, [] -> failwith "impossible: acc starts off non-empty"
        | [], _ -> List.rev acc
        | hd::tl, acfst::actail ->
          if hd = c then helper tl ([]::acfst::actail)
          else helper tl ((hd::acfst)::actail)
      in helper lst [[]]
    let rec split_by_lengths lens lst = 
      match lens, lst with
      | len::tl, _ -> 
        let (front,tail) = ListExt.split_at (len+1) lst
        in front :: split_by_lengths tl tail
      | [], [] -> []
      | _ -> failwith "impossible: length mismatch"
    let lists2loose (parts : TightSel.part list) (combs : combinator list) =
      let combs = split_at_each LooseSel.comb combs in
      let parts = split_by_lengths (List.map List.length combs) parts in
      let tights = List.map TightSel.fromParts parts in
      LooseSel.SetOfSel.singleton (LooseSel.fromParts tights)

    let pairings inter s t =
      let inter s t = LooseSel.lift (TightSel.lift (inter s t)) in
      let (s1parts, s1combs) = loose2lists s in
      let (s2parts, s2combs) = loose2lists t in
      let rec pair_off spartsrev scombsrev tpartsrev tcombsrev (endOfSel : LooseSel.SetOfSel.t) =
        assert (List.length spartsrev = List.length scombsrev &&
            List.length tpartsrev = List.length tcombsrev);
        match spartsrev, scombsrev, tpartsrev, tcombsrev with
        | [], [], [], [] -> endOfSel
        | _::_, [], _, _
        | _, _, _::_, [] -> failwith "ran out of combinators"
        | [], _::_, _, _
        | _, _, [], _::_ -> failwith "ran out of components"
        | [], [], _::_, tc::tcfrontrev -> 
          LooseSel.concat tc (lists2loose (List.rev tpartsrev) (List.rev tcfrontrev)) endOfSel
        | _::_, sc::scfrontrev, [], [] -> 
          LooseSel.concat sc (lists2loose (List.rev spartsrev) (List.rev scfrontrev)) endOfSel
        | sN::sfrontrev, scomb::scfrontrev, tM::tfrontrev, tcomb::tcfrontrev ->
          if scomb = TightSel.comb && tcomb = TightSel.comb then
            (* s = sfront (scfront) sN ( * ) ___ *)
            (* t = tfront (tcfront) tM ( * ) ___ *)
            let merged = 
              (* (pair_off sfront scfront tfront tcfront) (endComb) ((inter sN tM) ( * ) endOfSel) *)
              let last = LooseSel.concat TightSel.comb (inter sN tM) endOfSel in
              pair_off sfrontrev scfrontrev tfrontrev tcfrontrev last in
            merged
          else if scomb = TightSel.comb && tcomb = LooseSel.comb then
            (* s = sfront (scfront) sN ( * ) ___ *)
            (* t = tfront (tcfront) tM (+) ___ *)
            let merged = 
              (* (pair_off sfront scfront tfront tcfront) (endComb) ((inter sN tM) ( * ) endOfSel) *)
              let last = LooseSel.concat TightSel.comb (inter sN tM) endOfSel in
              pair_off sfrontrev scfrontrev tfrontrev tcfrontrev last in
            let sfirst =
              (* (pair_off sfront scfront tparts tcombs) ( * ) (sN (endComb) endOfSel) *)
              let last = LooseSel.concat TightSel.comb 
                (LooseSel.lift (TightSel.lift (TightSel.SetOfPart.singleton sN))) endOfSel in
              pair_off sfrontrev scfrontrev tpartsrev tcombsrev last in
            LooseSel.SetOfSel.union merged sfirst
          else if scomb = LooseSel.comb && tcomb = TightSel.comb then
            (* s = sfront (scfront) sN (+) ___ *)
            (* t = tfront (tcfront) tM ( * ) ___ *)
            let merged = 
              (* (pair_off sfront scfront tfront tcfront) (endComb) ((inter sN tM) ( * ) endOfSel) *)
              let last = LooseSel.concat TightSel.comb (inter sN tM) endOfSel in
              pair_off sfrontrev scfrontrev tfrontrev tcfrontrev last in
            let tfirst =
              (* (pair_off sparts scombs tfront tcfront) ( * ) (tM (endComb) endOfSel) *)
              let last = LooseSel.concat TightSel.comb 
                (LooseSel.lift (TightSel.lift (TightSel.SetOfPart.singleton tM))) endOfSel in
              pair_off spartsrev scombsrev tfrontrev tcfrontrev last in
            LooseSel.SetOfSel.union merged tfirst
          else 
            (* s = sfront (scfront) sN (+) ___ *)
            (* t = tfront (tcfront) tM (+) ___ *)
            let merged = 
              (* (pair_off sfront scfront tfront tcfront) (endComb) ((inter sN tM) (+) endOfSel) *)
              let last = LooseSel.concat LooseSel.comb (inter sN tM) endOfSel in
              pair_off sfrontrev scfrontrev tfrontrev tcfrontrev last in
            let sfirst =
              (* (pair_off sfront scfront tparts tcombs) (+) (sN (endComb) endOfSel) *)
              let last = LooseSel.concat LooseSel.comb 
                (LooseSel.lift (TightSel.lift (TightSel.SetOfPart.singleton sN))) endOfSel in
              pair_off sfrontrev scfrontrev tpartsrev tcombsrev last in
            let tfirst =
              (* (pair_off sparts scombs tfront tcfront) (+) (tM (endComb) endOfSel) *)
              let last = LooseSel.concat LooseSel.comb 
                (LooseSel.lift (TightSel.lift (TightSel.SetOfPart.singleton tM))) endOfSel in
              pair_off spartsrev scombsrev tfrontrev tcfrontrev last in
            LooseSel.SetOfSel.union merged (LooseSel.SetOfSel.union sfirst tfirst)
      in match List.rev s1parts, List.rev s2parts with
      | [], _
      | _, [] -> failwith "impossible: no parts in selectors"
      | sN::stail, tM::ttail ->
        pair_off stail (List.rev s1combs) ttail (List.rev s2combs) (inter sN tM)
  end


  (* module Pairings (LooseSel : UniformSelector) (TightSel : UniformSelector with type sel = LooseSel.part) = struct *)
  (*   let pairings inter s t = *)
  (*     let rec pair_off ss ts = *)
  (*       match List.rev ss, List.rev ts with *)
  (*       | [], _ -> LooseSel.SetOfSel.singleton (LooseSel.fromParts [t]) *)
  (*       | _, [] -> failwith "impossible15" *)
  (*       | ssrev, [t] -> Printf.printf "PCase1\n"; *)
  (*         let clause1 =  *)
  (*           LooseSel.SetOfSel.singleton (LooseSel.fromParts (ss @ [TightSel.fromParts [t]])) in (\* 4T *\) *)
  (*         let clause2 = match ssrev with  *)
  (*           | [] -> LooseSel.SetOfSel.empty *)
  (*           | sN::sfrontrev ->  *)
  (*             let sfrontSet = match List.rev sfrontrev with *)
  (*               | [] -> LooseSel.SetOfSel.empty *)
  (*               | sfront -> LooseSel.SetOfSel.singleton (LooseSel.fromParts sfront) in *)
  (*             LooseSel.concat LooseSel.comb sfrontSet *)
  (*               (LooseSel.lift (inter sN (TightSel.fromParts [t]))) in *)
  (*         LooseSel.SetOfSel.union clause1 clause2 *)
  (*       | sN::sfrontrev, tM::_ -> Printf.printf "PCase2\n"; *)
  (*         let sfront = List.rev sfrontrev in *)
  (*         let sNLen = List.length (TightSel.toParts sN) in *)
  (*         let (tfront, ttail) = ListExt.split_at (List.length ts - sNLen) ts in *)
  (*         let clause1 = LooseSel.SetOfSel.empty in *)
  (*           (\* let tail = (LooseSel.SetOfSel.singleton (LooseSel.fromParts [TightSel.fromParts [tM]])) in *\) *)
  (*           (\* match tfront with *\) *)
  (*           (\* | [] -> LooseSel.concat LooseSel.comb (LooseSel.SetOfSel.singleton (LooseSel.fromParts sfront)) tail *\) *)
  (*           (\* | _ -> LooseSel.concat TightSel.comb (pair_off ss tfront) tail in *\) *)
  (*         let clause2 = *)
  (*           let tail = (LooseSel.lift (inter sN (TightSel.fromParts ttail))) in *)
  (*           match tfront with *)
  (*           | [] -> LooseSel.concat TightSel.comb (LooseSel.SetOfSel.singleton (LooseSel.fromParts sfront)) tail *)
  (*           | _ -> (\* TODO: This case is wrong *\) LooseSel.concat TightSel.comb (pair_off sfront tfront) tail in *)
  (*         LooseSel.SetOfSel.union clause1 clause2 in *)
  (*     let ss = LooseSel.toParts s in *)
  (*     let ts = TightSel.toParts t in *)
  (*     (match List.rev ss, ts with *)
  (*     | sN::((_::_) as sfrontrev), _::_ ->  *)
  (*       let sfront = List.rev sfrontrev in *)
  (*       let sNLen = List.length (TightSel.toParts sN) in *)
  (*       let (tfront, ttail) = ListExt.split_at (List.length ts - sNLen) ts in *)
  (*       let last = LooseSel.lift (inter sN (TightSel.fromParts ttail)) in *)
  (*       begin match tfront with *)
  (*       | [] -> LooseSel.concat LooseSel.comb (LooseSel.SetOfSel.singleton (LooseSel.fromParts sfront)) last *)
  (*       | _ -> *)
  (*         let paired = (pair_off sfront tfront) in *)
  (*         LooseSel.concat TightSel.comb paired last (\* (LooseSel.concat TightSel.comb last last) (\* LAST LAST *\) *\) *)
  (*       end *)
  (*     | _, _ -> failwith "impossible16") *)
  (* end *)

  let canonical (s1a, s1s) (s2a, s2s) = 
    if (s1a <> s2a) then SimpleSet.empty
    else 
      let specs = ListExt.remove_dups (s1s @ s2s) in
      if (List.length (List.filter (fun s -> match s with SpId _ -> true | _ -> false) specs) > 1)
      then SimpleSet.empty
      else SimpleSet.singleton (s1a, specs)

  let rec intersect_sels s1 s2 =
    let rec simple_inter s1 s2 = canonical s1 s2
    and adj_inter a1 a2 = 
      if a1 = a2 then AdjSet.singleton a1 else
      let module Simple2Adj = Map2Sets(SimpleSet)(AdjSet) in 
      match a1, a2 with
      | A (a1a, a1s), AS a2s -> 
        Simple2Adj.map (fun s -> A(a1a, s)) (simple_inter a1s a2s)
      | A (a1a, a1s), A (a2a, a2s) -> 
        let module AdjSimplCross = Cross2Sets (AdjSet)(SimpleSet)(AdjSet) in
        AdjSimplCross.cross (fun a s -> A(a, s)) (adj_inter a1a a2a) (simple_inter a1s a2s)
      | AS s1, AS s2 -> Simple2Adj.map (fun s -> AS s) (simple_inter s1 s2)
      | _ -> adj_inter a2 a1
    and sib_inter s1 s2 = 
      if s1 = s2 then SibSet.singleton s1 else
      let module Adj2Sib = Map2Sets(AdjSet)(SibSet) in
      match s1, s2 with
      | S(s1s, s1a), SA (AS s2s) -> 
        Adj2Sib.map (fun a -> S(s1s, a)) (adj_inter s1a (AS s2s))
      | S(s1s, s1a), SA (A (a2a, a2s)) -> pairings_sib s1 s2
      | S(s1s, s1a), S (s2s, s2a) -> pairings_sib s1 s2
      | SA a1, SA a2 -> Adj2Sib.map (fun a -> SA a) (adj_inter a1 a2)
      | _ -> sib_inter s2 s1
    and kid_inter k1 k2 = 
      let open FormatExt in
      let open Format in
      let answer = if k1 = k2 then KidSet.singleton k1 else
        let module Sib2Kid = Map2Sets (SibSet) (KidSet) in
        match k1, k2 with
        | K(k1k, k1s), KS s -> Printf.printf "KCase1\n";
          Sib2Kid.map (fun s -> K(k1k, s)) (sib_inter k1s s)
        | K(k1k, k1s), K (k2k, k2s) ->Printf.printf "KCase2\n";
          let module KidSibCross = Cross2Sets (KidSet) (SibSet) (KidSet) in
          KidSibCross.cross (fun k s -> K(k,s)) (kid_inter k1k k2k) (sib_inter k1s k2s)
        | KS s1, KS s2 -> Printf.printf "KCase3\n"; Sib2Kid.map (fun s -> KS s) (sib_inter s1 s2)
        | _ -> Printf.printf "KCase4\n"; kid_inter k2 k1
      in
      vert [label "k1:" [Pretty.pretty_kid k1];
            label "k2:" [Pretty.pretty_kid k2];
            label "int:" [KidSetExt.p_set Pretty.pretty_kid answer]] std_formatter; print_newline();
      answer
    and desc_inter d1 d2 =
      let open FormatExt in
      let open Format in
      let answer = if d1 = d2 then SelSet.singleton d1 else
      let module Kid2Desc = Map2Sets (KidSet) (SelSet) in
      match d1, d2 with
      | D(d1d, d1k), DK (KS s) -> Printf.printf "DCase1\n";
        Kid2Desc.map (fun k -> D(d1d, k)) (kid_inter d1k (KS s))
      | D(d1d, d1k), DK (K (d2k, d2s)) -> Printf.printf "DCase2\n"; pairings_desc d1 s2
      | D(d1d, d1k), D(d2d, d2k) -> Printf.printf "DCase3\n"; pairings_desc d1 d2
      | DK k1, DK k2 -> Printf.printf "DCase4\n"; Kid2Desc.map (fun k -> DK k) (kid_inter k1 k2)
      | _ -> Printf.printf "DCase5\n"; desc_inter d2 d1
      in
      vert [label "d1:" [Pretty.pretty_sel d1];
            label "d2:" [Pretty.pretty_sel d2];
            label "int:" [SelSetExt.p_set Pretty.pretty_sel answer]] std_formatter; print_newline();
      answer

    (* and interleavings_sib s t =  *)
    (*   let module InterSib = Interleavings (SibSelector) in *)
    (*   InterSib.interleavings sib_inter s t *)
        
    (* and interleavings_desc s t =  *)
    (*   let module InterDesc = Interleavings (DescSelector) in *)
    (*   InterDesc.interleavings desc_inter s t *)

    and pairings_sib s1 s2 = 
      let module PairingsSibAdj = Pairings (SibSelector) (AdjSelector) in
      PairingsSibAdj.pairings simple_inter s1 s2

    and pairings_desc d1 d2 =
      let module PairingsDescKid = Pairings (DescSelector) (KidSelector) in
      PairingsDescKid.pairings sib_inter d1 d2 in
    
    (* actually do the intersection! *) 
    desc_inter s1 s2
      
  let intersect s1 s2 = 
    let module SelSetSet = Set.Make(SelSet) in
    let module SelSelCross = Cross2Sets (SelSet) (SelSet) (SelSetSet) in
    let inters = SelSelCross.cross intersect_sels s1 s2 in
    SelSetSet.fold SelSet.union inters SelSet.empty
  let intersections ss = match ss with 
    | [] -> SelSet.empty
    | hd::tl -> List.fold_left intersect hd tl
  let union = SelSet.union
  let unions ss = List.fold_left union SelSet.empty ss
  let negate _ = SelSet.empty
  let subtract = SelSet.diff
  let singleton s = empty (* TODO *)
  let singleton_string _ = None
  let var _ = SelSet.empty
  let is_subset (_ : 'a IdMap.t) s1 s2 =
    Specificity.is_morespecific s1 s2 (* || begin *)
    (*   let make_regex s = *)
    (*     R.unions (List.map AsRegex.sel2regex (SelSetExt.to_list s)) in *)
    (*   if SelSet.is_empty s1 then true else if SelSet.is_empty s2 then false else *)
    (*       (\* remove any obvious overlap *\) *)
    (*       let (s1, s2) = (SelSet.diff s1 s2, SelSet.diff s2 s1) in *)
    (*       if SelSet.is_empty s1 then true else if SelSet.is_empty s2 then false else *)
    (*           let r1 = make_regex s1 in *)
    (*           let r2 = make_regex s2 in *)
    (*           let open FormatExt in *)
    (*           horzOrVert [text (R.pretty r1); text "<="; text (R.pretty r2)] Format.std_formatter; *)
    (*           Format.print_newline(); *)
    (*           R.is_subset r1 r2 *)
    (* end *)
    
  let pretty_sel s = Pretty.pretty_sel s
  let p_css t =
    if SelSet.cardinal t = 1
    then pretty_sel (SelSet.choose t)
    else SelSetExt.p_set pretty_sel t




  let n = ref (-1)
  let fresh_var () = (* a, b, ... z, aa, bb, ..., zz, ... *)
    incr n;
    String.make (1 + (!n / 26)) (Char.chr (Char.code 'a' + (!n mod 26)))

  let random_regsel len = 
    let random_simple () : simple = (TSel (fresh_var ()), []) in
    let random_comb () = match Random.int 4 with
      | 0 -> Adj
      | 1 -> Sib
      | 2 -> Kid
      | _ -> Desc in
    match List.map (fun _ -> (random_comb (), random_simple ())) (iota len) with
    | [] -> []
    | (_,s)::tl -> (Desc,s)::tl
      
  let random_sel len =
    let rec random_simple () = (TSel (fresh_var ()), []) 
    and random_adj len =
      if len = 0 then AS (random_simple ()) else
        A (random_adj (len - 1), random_simple ()) 
    and random_sib len =
      if len = 0 then SA (random_adj len) else
        let split = Random.int len in
        S (random_sib split, random_adj (len - split - 1)) 
    and random_kid len =
      if len = 0 then KS (random_sib len) else
        let split = Random.int len in
        K (random_kid split, random_sib (len - split - 1)) 
    and random_desc len =
      if len = 0 then DK (random_kid len) else
        let split = Random.int len in
        D (random_desc split, random_kid (len - split - 1)) in
    random_desc len

  let rec testSels num = 
    let testRegsel r =
      let open FormatExt in
      label "Unprec:"  [horz [Pretty.pretty_regsel r; text "="];
                        Pretty.pretty_regsel (desc2regsel (regsel2desc r))]
        Format.std_formatter; 
      Format.print_newline ();
      desc2regsel (regsel2desc r) = r in
    let testSel s =
      let open FormatExt in
      label "Prec:  " [horz [Pretty.pretty_sel s; text "="];
                       Pretty.pretty_sel (regsel2desc (desc2regsel s))]
        Format.std_formatter; 
      Format.print_newline ();
      regsel2desc (desc2regsel s) = s in
    let testInter s1 s2 =
      let open FormatExt in
      let s1 = SelSet.singleton s1 in
      let s2 = SelSet.singleton s2 in
      let sInter = intersect s1 s2 in
      vert [label "s1:" [p_css s1];
            label "s2:" [p_css s2];
            label "sInter:" [p_css sInter]] Format.std_formatter;
      Format.print_newline();
      if not (is_subset IdMap.empty sInter s1) then begin
        label "sInter <!= s1:" [vert [label "s1:    " [p_css s1];
                                      label "sInter:" [p_css sInter]]] Format.std_formatter;
        Format.print_newline (); false
      end else true &&
      if not (is_subset IdMap.empty sInter s2) then begin
        label "sInter <!= s2:" [vert [label "s2:    " [p_css s2];
                                      label "sInter:" [p_css sInter]]] Format.std_formatter;
        Format.print_newline (); false
      end else true in
    if num >= 0 then begin
      (* s1:e (d > c) b a
         s2:d (c > b > a) *)
      let m2a x = AS (TSel x , []) in
      let m2s x = SA (m2a x) in
      let m2k x = KS (m2s x) in
      let m2d x = DK (m2k x) in
      (* let s1 = DK (K(KS(S(S(m2s "e", m2a "d"), m2a "c")), m2s "b")) in *)
      (* let s2 = D (m2d "f", K(m2k "c", m2s "b")) in *)
      let s1 = D(D(D(m2d "e", K(m2k "d", m2s "c")), m2k "b"), m2k "a") in
      let s2 = D(m2d "d", K(K(m2k "c", m2s "b"), m2s "a")) in
      testInter s1 s2
    end else begin
      n := -1;
      let r = random_regsel (1 + Random.int 10) in
      n := -1;
      let s = random_sel (1 + Random.int 10) in
      n := -1;
      let t = random_sel (1 + Random.int 10) in
      (testRegsel r) && (testSel s) && (testInter s t) && (testSels (num-1))
    end


  let pretty s = (SelSetExt.p_set Pretty.pretty_sel s Format.str_formatter; Format.flush_str_formatter())
  let is_empty s = SelSet.exists (fun sel -> 
    (List.exists (fun sim -> not (SimpleSet.is_empty (canonical sim sim))) (List.map snd (desc2regsel sel)))) s
  let is_overlapped s1 s2 = 
    not (SelSet.is_empty (intersect s1 s2))
  let is_equal s1 s2 = (is_subset IdMap.empty s1 s2) && (is_subset IdMap.empty s2 s1)
  let example s = 
    let pretty_sel s = (Pretty.pretty_sel s Format.str_formatter; Format.flush_str_formatter()) in
    try Some (pretty_sel (SelSet.choose s)) with Not_found -> None
end
