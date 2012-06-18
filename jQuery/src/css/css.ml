open Prelude
open Sig
open SetExt

module type CSS = sig
  include  SET
  type combinator = Desc | Kid | Sib | Adj
  val concat_selectors : t -> combinator -> t -> t
  val p_css : t -> FormatExt.printer
end

module DummyCSS : CSS = struct
  type combinator = Desc | Kid | Sib | Adj
  type sel = ()
  module SelOrdered = struct
    type t = sel
    let compare = compare
  end
  module SelSet = Set.Make (SelOrdered)
  module SelSetExt = SetExt.Make (SelSet)
  type t = SelSet.t
  let parse _ _ = SelSet.empty
  let empty = SelSet.empty
  let all = SelSet.singleton ()
  let intersect _ _ = SelSet.empty
  let intersections _ = SelSet.empty
  let union _ _ = SelSet.empty
  let unions _ = SelSet.empty
  let negate _ = SelSet.empty
  let subtract _ _ = SelSet.empty
  let singleton _ = SelSet.empty
  let singleton_string _ = None
  let var _ = SelSet.empty
  let pretty _ = "()"
  let is_empty _ = true
  let is_overlapped _ _ = true
  let is_subset _ _ _ = true
  let is_equal _ _ = true
  let example _ = None

  let concat_selectors _ _ _ = SelSet.empty
  let pretty_sel s = FormatExt.text "(|dummy|)"
  let p_css t = 
    if SelSet.cardinal t = 1 
    then pretty_sel (SelSet.choose t)
    else SelSetExt.p_set pretty_sel t
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

module RealCSS : CSS = struct
  type atomic = TSel of string | USel
  and spec = | SpId of string | SpClass of string
	     | SpAttrib of string | SpPseudo of string
  and simple = atomic * spec list
  and adj = A of adj * simple | AS of simple
  and sib = S of sib * adj | SA of adj
  and kid = K of kid * sib | KS of sib
  and desc = D of desc * kid | DK of kid
  and sel = desc
  let rec adj2list a = begin match a with AS s -> [s] | A(a, s) -> List.append (adj2list a) [s]  end
  (* ... and for the others, too ... *)
  type combinator = Desc | Kid | Sib | Adj
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
  type t = SelSet.t
  let parse _ _ = SelSet.empty
  let empty = SelSet.empty
  let all = SelSet.singleton (DK (KS (SA (AS (USel, [])))))
  let adj a s  = A (a, s)
  let sib s a = S (s, a)
  let kid c s =  K (c, s)
  let desc d c = D (d, c)
  let rec intersect_sels (s1 : sel) (s2 : sel) =
    let wrapSimple s = (DK (KS (SA (AS s)))) in
    let wrapAdj a = (DK (KS (SA a))) in
    let wrapSib sib = (DK (KS sib)) in
    let rec simple_inter s1 s2 = canonical s1 s2
    and adj_inter a1 a2 = 
      let module Simple2Adj = Map2Sets(SimpleSet)(AdjSet) in 
      match a1, a2 with
      | A (a1a, a1s), AS a2s -> 
        Simple2Adj.map (fun s -> adj a1a s) (simple_inter a1s a2s)
      | A (a1a, a1s), A (a2a, a2s) -> 
        let module AdjSimplCross = Cross2Sets (AdjSet)(SimpleSet)(AdjSet) in
        AdjSimplCross.cross adj (adj_inter a1a a2a) (simple_inter a1s a2s)
      | AS s1, AS s2 -> Simple2Adj.map (fun s -> AS s) (simple_inter s1 s2)
      | _ -> adj_inter a2 a1
    and sib_inter s1 s2 = 
      let module Adj2Sib = Map2Sets(AdjSet)(SibSet) in
      match s1, s2 with
      | S(s1s, s1a), SA (AS s2s) -> 
        Adj2Sib.map (sib s1s) (adj_inter s1a (AS s2s))
      | S(s1s, s1a), SA (A (a2a, a2s)) -> SibSet.empty (* pairings ... *)
      | S(s1s, s1a), S (s2s, s2a) -> SibSet.empty (* interleavings ... *)
      | SA a1, SA a2 -> Adj2Sib.map (fun a -> SA a) (adj_inter a1 a2)
      | _ -> sib_inter s2 s1
    and kid_inter k1 k2 = 
      let module Sib2Kid = Map2Sets (SibSet) (KidSet) in
      match k1, k2 with
      | K(k1k, k1s), KS s -> 
        Sib2Kid.map (kid k1k) (sib_inter k1s s)
      | K(k1k, k1s), K (k2k, k2s) ->
        let module KidSibCross = Cross2Sets (KidSet) (SibSet) (KidSet) in
        KidSibCross.cross kid (kid_inter k1k k2k) (sib_inter k1s k2s)
      | KS s1, KS s2 -> Sib2Kid.map (fun s -> KS s) (sib_inter s1 s2)
      | _ -> kid_inter k2 k1
    and desc_inter d1 d2 =
      let module Kid2Desc = Map2Sets (KidSet) (SelSet) in
      match d1, d2 with
      | D(d1d, d1k), DK (KS s) ->
        Kid2Desc.map (desc d1d) (kid_inter d1k (KS s))
      | D(d1d, d1k), DK (K (d2k, d2s)) -> SelSet.empty (* pairings ... *)
      | D(d1d, d1k), D(d2d, d2k) -> SelSet.empty (* interleavings ... *)
      | DK k1, DK k2 -> Kid2Desc.map (fun k -> DK k) (kid_inter k1 k2)
      | _ -> desc_inter d2 d1
    and canonical (s1a, s1s) (s2a, s2s) = 
      if (s1a != s2a) then SimpleSet.empty
      else (* TODO *) SimpleSet.empty
      
    and interleavings (c : combinator) (s1 : sel) (s2 : sel) = SelSet.empty
    and pairings (c1 : combinator) (c2 : combinator) (s1 : sel) (s2 : sel) = SelSet.empty
    and pairoff  (c1 : combinator) (c2 : combinator) (s1 : sel) (s2 : sel) = SelSet.empty
    in SelSet.empty
  let intersect s1 s2 = 
    let module SelSetSet = Set.Make(SelSet) in
    let module SelSelCross = Cross2Sets (SelSet) (SelSet) (SelSetSet) in
    let inters = SelSelCross.cross intersect_sels s1 s2 in
    SelSetSet.fold SelSet.union inters SelSet.empty
  let intersections _ = SelSet.empty
  let union _ _ = SelSet.empty
  let unions _ = SelSet.empty
  let negate _ = SelSet.empty
  let subtract _ _ = SelSet.empty
  let singleton _ = SelSet.empty
  let singleton_string _ = None
  let var _ = SelSet.empty
  let pretty _ = "()"
  let is_empty _ = true
  let is_overlapped _ _ = true
  let is_subset _ _ _ = true
  let is_equal _ _ = true
  let example _ = None

  let concat_selectors s1 comb s2 = SelSet.empty
    (* let module SelSetSet = Set.Make(SelSet) in *)
    (* let module SelSelCross = Cross2Sets (SelSet) (SelSet) (SelSetSet) in *)
    (* let inters = SelSelCross.cross (match comb with Adj -> adj | Sib -> sib | Kid -> kid | _ -> desc) s1 s2 in *)
    (* SelSetSet.fold SelSet.union inters SelSet.empty *)
    
  let pretty_sel s = FormatExt.text "(|dummy|)"
  let p_css t =
    if SelSet.cardinal t = 1
    then pretty_sel (SelSet.choose t)
    else SelSetExt.p_set pretty_sel t
end
