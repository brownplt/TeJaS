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

module RealCSS = struct


  type atomic = TSel of string | USel
  and spec = | SpId of string | SpClass of string
             | SpAttrib of string | SpPseudo of string
  and simple = atomic * spec list
  and adj = A of adj * simple | AS of simple
  and sib = S of sib * adj | SA of adj
  and kid = K of kid * sib | KS of sib
  and desc = D of desc * kid | DK of kid
  and sel = desc

  module Pretty = struct
    open FormatExt
    let rec pretty_atomic a =
      match a with 
      | USel -> text "*"
      | TSel t -> text t
    and pretty_simple (a, _) = pretty_atomic a
    and pretty_adj a = match a with
      | AS s -> pretty_simple s
      | A (a, s) -> horzOrVert [pretty_adj a; text "+"; pretty_simple s]
    and pretty_sib s = match s with
      | SA a -> pretty_adj a
      | S (s, a) -> horzOrVert [pretty_sib s; text "~"; pretty_adj a]
    and pretty_kid k = match k with
      | KS s -> pretty_sib s
      | K (k, s) -> horzOrVert [pretty_kid k; text ">"; pretty_sib s]
    and pretty_desc d = match d with
      | DK k -> pretty_kid k
      | D (d, k) -> horzOrVert [pretty_desc d;  pretty_kid k]
    let pretty_sel = pretty_desc
  end
  type combinator = Desc | Kid | Sib | Adj

  type regsel = simple * ((combinator * simple) list)

  let sel2regsel s = 
    let rec simple2regsel s = [Desc, s]
    and adj2regsel a = match a with
      | AS s -> simple2regsel s
      | A(a, s) -> match adj2regsel a, simple2regsel s with
        | ra, (_,s)::tl -> ra @ (Adj, s) :: tl
        | _ -> failwith "impossible"
    and sib2regsel s = match s with
      | SA a -> adj2regsel a
      | S(s, a) -> match sib2regsel s, adj2regsel a with
        | rs, (_, a)::tl -> rs @ (Sib, a) :: tl
        | _ -> failwith "impossible"
    and kid2regsel k = match k with
      | KS s -> sib2regsel s
      | K(k, s) -> match kid2regsel k, sib2regsel s with
        | rk, (_,s)::tl -> rk @ (Kid, s) :: tl
        | _ -> failwith "impossible"
    and desc2regsel d = match d with
      | DK k -> kid2regsel k
      | D(d, k) -> match desc2regsel d, kid2regsel k with
        | rd, (_, k)::tl -> rd @ (Desc, k) :: tl
        | _ -> failwith "impossible"
    in match desc2regsel s with
    | [] -> failwith "impossible"
    | (_, s)::tl -> (s, tl)

  let regsel2sel (rs : regsel) =
    let al = let (s, l) = rs in
      List.map (fun (c, s) -> (c, AS s)) ((Desc, s)::l) in
    let rec s2a al = match al with
      | [] -> []
      | (c, a1)::(Adj, (AS s2))::tl -> s2a ((c, A(a1, s2))::tl)
      | (c, a1)::tl -> (c, a1)::s2a tl in
    let sl = List.map (fun (c, a) -> (c, SA a)) (s2a al) in
    let rec a2sib sl = match sl with
      | [] -> []
      | (c, s1)::(Sib, (SA a2))::tl -> a2sib ((c, S(s1, a2))::tl)
      | (c, s1)::tl -> (c, s1)::a2sib tl in
    let kl = List.map (fun (c, s) -> (c, KS s)) (a2sib sl) in
    let rec s2k kl = match kl with
      | [] -> []
      | (c, k1)::(Kid, (KS s2))::tl -> s2k ((c, K(k1, s2))::tl)
      | (c, k1)::tl -> (c, k1)::s2k tl in
    let dl = List.map (fun (c, k) -> (c, DK k)) (s2k kl) in
    let rec k2d dl = match dl with
      | [] -> []
      | (c, d1)::(Desc, (DK k2))::tl -> k2d ((c, D(d1, k2))::tl)
      | (c, d1)::tl -> (c, d1)::k2d tl in 
    match (k2d dl) with
        | [(Desc, d)] -> d
        | _ -> failwith "impossible"

  let n = ref (-1)
  let fresh_var () = (* a, b, ... z, aa, bb, ..., zz, ... *)
    incr n;
    String.make (1 + (!n / 26)) (Char.chr (Char.code 'a' + (!n mod 26)))

  let random_regsel len = 
    let random_simple () = (TSel (fresh_var ()), []) in
    let random_comb () = match Random.int 4 with
      | 0 -> Adj
      | 1 -> Sib
      | 2 -> Kid
      | _ -> Desc in
    (random_simple (), List.map (fun _ -> (random_comb (), random_simple ())) (iota len))
      
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
      sel2regsel (regsel2sel r) = r in
    let testSel s =
      let open FormatExt in
      horzOrVert [horz [Pretty.pretty_sel s; text "="];
                  Pretty.pretty_sel (regsel2sel (sel2regsel s))] 
        Format.std_formatter; 
      Format.print_newline ();
      regsel2sel (sel2regsel s) = s in
    if num = 0 then true else begin
      n := -1;
      let r = random_regsel (Random.int 10) in
      let s = random_sel (Random.int 10) in
      (testRegsel r) && (testSel s) && (testSels (num-1))
    end


  let rec adj2list a = begin match a with AS s -> [s] | A(a, s) -> List.append (adj2list a) [s]  end
  (* ... and for the others, too ... *)

      


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

  let concat_sels (s1 : desc) (comb : combinator) (s2 : desc) : desc = 
    let (rs1, rs1tl) = sel2regsel s1 in
    let (rs2, rs2tl) = sel2regsel s2 in
    regsel2sel (rs1, rs1tl @ (comb, rs2) :: rs2tl)
 let concat_selectors s1 comb s2 =
    let module SelSelCross = Cross2Sets (SelSet) (SelSet) (SelSet) in
    SelSelCross.cross (fun s1 s2 -> concat_sels s1 comb s2) s1 s2
    (* SelSetSet.fold SelSet.union inters SelSet.empty *)
    
  let pretty_sel s = FormatExt.text "(|dummy|)"
  let p_css t =
    if SelSet.cardinal t = 1
    then pretty_sel (SelSet.choose t)
    else SelSetExt.p_set pretty_sel t
end
