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
             | SpAttrib of string * (oper * string) option | SpPseudo of string
  and oper = AOEquals | AOStartsWith | AOEndsWith | AOPrefixedWith | AOContainsClass | AOSubstring
  and simple = atomic * spec list
  and adj = A of adj * simple | AS of simple
  and sib = S of sib * adj | SA of adj
  and kid = K of kid * sib | KS of sib
  and desc = D of desc * kid | DK of kid
  and sel = desc
  type combinator = Desc | Kid | Sib | Adj

  (* Collection functions *)

  let rev_collect_a a = 
    let rec rev_collect_a_h a acc = match a with
      | AS s -> s :: acc
      | A (a, s) -> rev_collect_a_h a (s :: acc) in
    rev_collect_a_h a []

  let collect_a a = List.rev (rev_collect_a a)

  let rev_collect_s s =
    let rec rev_collect_s_h s acc = match s with
      | SA a -> a :: acc
      | S (s, a) -> rev_collect_s_h s (a :: acc) in
    rev_collect_s_h s []

  let collect_s s = List.rev (rev_collect_s s)

  let rec uncollect_s alist = match alist with
    | [] -> failwith "impossible"
    | [a] -> SA a
    | a::tl -> S ((uncollect_s tl), a)

  let rev_collect_k k =       
    let rec rev_collect_k_h k acc = match k with
      | KS s -> s :: acc
      | K (k, s) -> rev_collect_k_h k (s :: acc) in
    rev_collect_k_h k []

  let collect_k k = List.rev (rev_collect_k k)
    
  let rev_collect_d d =
    let rec rev_collect_d_h d acc = match d with
      | DK k -> k :: acc
      | D (d, k) -> rev_collect_d_h d (k :: acc) in
    rev_collect_d_h d []

  let collect_d d = List.rev (rev_collect_d d)
    
  let rec uncollect_d lok = match lok with
    | [] -> failwith "impossible"
    | [k] -> DK k
    | k::tl -> D ((uncollect_d tl), k)

  (* END Collection functions *)
      
  module Pretty = struct
    open FormatExt
    let pretty_list p_item p_comb lst =
      (add_sep_between p_comb (List.rev_map p_item lst), List.length lst > 1)
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
      parensOrHOV (pretty_list pretty_simple (text " +") (rev_collect_a a))
    and pretty_sib s = 
      parensOrHOV (pretty_list pretty_adj (text " ~") (rev_collect_s s))
    and pretty_kid k = 
      parensOrHOV (pretty_list pretty_sib (text " >") (rev_collect_k k))
    and pretty_desc d = 
      horzOrVert (fst (pretty_list pretty_kid empty (rev_collect_d d)))
    let pretty_sel = pretty_desc
    let pretty_regsel (rs : ((combinator * simple) list)) =
      match rs with
      | [] -> failwith "impossible"
      | (c, s)::css ->
      let parens = enclose 1 "" empty (text "(") (text ")") in
      horzOrVert (List.fold_left 
                     (fun p (c, s) -> 
                       [squish [parens p; 
                                text (match c with
                                | Adj -> " +" | Sib -> " ~" 
                                | Kid -> " >" | _ -> "")];
                        pretty_simple s])
                     [pretty_simple s] css)
  end

  type regsel = ((combinator * simple) list)

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

  let (regsel2sib, regsel2desc) =
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
      | _ -> failwith "impossible" in
    let regsel2sib rs =
      match (adjs2sibs (regsel2adjs rs)) with
      | [(Sib, d)] -> d
      | _ -> failwith "impossible" in
    (regsel2sib, regsel2desc)

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
    List.map (fun _ -> (random_comb (), random_simple ())) (iota len)
      
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
                        Pretty.pretty_regsel (sel2regsel (regsel2sel r))]
        Format.std_formatter; 
      Format.print_newline ();
      desc2regsel (regsel2desc r) = r in
    let testSel s =
      let open FormatExt in
      label "Prec:  " [horz [Pretty.pretty_sel s; text "="];
                       Pretty.pretty_sel (regsel2sel (sel2regsel s))]
        Format.std_formatter; 
      Format.print_newline ();
      regsel2desc (desc2regsel s) = s in
    if num = 0 then true else begin
      n := -1;
      let r = random_regsel (Random.int 10) in
      n := -1;
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

  let concat_selectors_gen toRegsel1 fromRegsel cross s1 comb s2 =
    let helper d1 comb d2 =
      let rd1 = toRegsel1 d1 in
      let rd2 = toRegsel1 d2 in
      fromRegsel (rd1 @ (comb, (snd (List.hd rd2))) :: (List.tl rd2)) in
    cross (fun s1 s2 -> helper s1 comb s2) s1 s2
  let concat_selectors = 
    let module SelSelCross = Cross2Sets (SelSet) (SelSet) (SelSet) in
    concat_selectors_gen  desc2regsel regsel2desc SelSelCross.cross
  let concat_sibs comb s1 s2 = 
    let module SibSibCross = Cross2Sets (SibSet) (SibSet) (SibSet) in
    concat_selectors_gen  sib2regsel regsel2sib SibSibCross.cross s1 comb s2
  let concat_descs comb s1 s2 = concat_selectors s1 comb s2

  let adj a s  = A (a, s)
  let sib s a = S (s, a)
  let kid c s =  K (c, s)
  let desc d c = D (d, c)

  let rec interleavings inter_single sel2list unsel2list singleton concat union empty
      s t =
    let interleavings = 
      interleavings inter_single sel2list unsel2list singleton concat union empty in
    let slist = sel2list s in
    let tlist = sel2list t in
    match slist, tlist with
    | [], _
    | _, [] -> failwith "impossible"
    | [_], _
    | _, [_] -> inter_single s t
    | s1::s2N, t1::t2M ->
      let clause1 =
        let s1set = singleton s1 in
        let inter1 = interleavings (unsel2list s2N) t in
        concat s1set inter1 in
      let clause2 =
        let t1set = singleton t1 in
        let inter2 = interleavings s (unsel2list t2M) in
        concat t1set inter2 in
      let clause3 =
        let inter_lists ss ts = 
          interleavings (unsel2list ss) (unsel2list ts) in
        List.fold_left union empty
          (List.map (fun i ->
            List.fold_left union empty
              (List.map (fun j ->
                let (s1i, siN) = ListExt.split_at i slist in
                let (t1j, tjM) = ListExt.split_at j tlist in
                let inter_ij = inter_lists s1i t1j in
                let inter_NM = inter_lists siN tjM in
                concat inter_ij inter_NM
               ) (iota (List.length tlist - 1)))
           ) (iota (List.length slist - 1))) in
      union clause1 (union clause2 clause3)

  let pairings raise1 raise2 comb1 comb2 empty union singleton 
      inter collect1 collect2 uncollect2 concat s t =
    let rec pair_off ss ts =
      match List.rev ss, List.rev ts with
      | [], _ -> singleton (raise2 t)
      | _, [] -> failwith "impossible"
      | ssrev, [t] ->
        let clause1 = 
          singleton (uncollect2 (ss @ [(raise1 t)])) in
        let clause2 = match ssrev with 
          | [] -> empty
          | sN::sfrontrev -> 
            let sfront = List.rev sfrontrev in
            concat comb1 (singleton (uncollect2 sfront))
              (inter (raise2 sN) (raise2 (raise1 t))) in
        union clause1 clause2
      | sN::sfrontrev, tM::tfrontrev ->
        let sfront = List.rev sfrontrev in
        let tfront = List.rev tfrontrev in
        let clause1 = concat comb2 (pair_off ss tfront)
          (singleton (raise2 (raise1 tM))) in
        let clause2 = concat comb2 (pair_off sfront tfront)
          (inter (raise2 sN) (raise2 (raise1 tM))) in
        union clause1 clause2 in
    let ss = collect2 s in
    let ts = collect1 t in
    (match List.rev ss, List.rev ts with
    | sN::(_::_ as sfrontrev), tM::(_::_ as tfrontrev) -> 
      let sfront = List.rev sfrontrev in
      let tfront = List.rev tfrontrev in
      concat comb2 (pair_off sfront tfront) 
        (inter (raise2 sN) (raise2 (raise1 tM)))
    | _, _ -> failwith "impossible")

  let rec intersect_sels s1 s2 =
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
      | S(s1s, s1a), SA (A (a2a, a2s) as a2) -> pairings_sib_adj s1 a2
      | S(s1s, s1a), S (s2s, s2a) -> interleavings_sib s1 s2
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
      | D(d1d, d1k), DK (K (d2k, d2s) as k2) -> pairings_desc_child d1 k2
      | D(d1d, d1k), D(d2d, d2k) -> interleavings_desc d1 d2
      | DK k1, DK k2 -> Kid2Desc.map (fun k -> DK k) (kid_inter k1 k2)
      | _ -> desc_inter d2 d1
    and canonical (s1a, s1s) (s2a, s2s) = 
      if (s1a != s2a) then SimpleSet.empty
      else (* TODO *) SimpleSet.empty
        
    and interleavings_sib s t = 
      interleavings sib_inter collect_s uncollect_s
        (fun a -> SibSet.singleton (SA a))
        (concat_sibs Sib) SibSet.union SibSet.empty s t
        
    and interleavings_desc s t = 
      interleavings desc_inter collect_d uncollect_d
        (fun k -> SelSet.singleton (DK k))
        (concat_descs Desc) SelSet.union SelSet.empty s t

    and pairings_sib_adj s t = 
      pairings (fun s -> (AS s)) (fun a -> (SA a)) Sib Adj SibSet.empty
        SibSet.union SibSet.singleton sib_inter collect_a collect_s 
        uncollect_s concat_sibs
        s t
    and pairings_desc_child d k =
      pairings (fun s -> (KS s)) (fun k -> (DK k)) Desc Kid SelSet.empty
        SelSet.union SelSet.singleton desc_inter collect_k collect_d
        uncollect_d concat_descs
        d k in
    
    (* actually do the intersection! *) 
    desc_inter s1 s2
      
  let intersect s1 s2 = 
    let module SelSetSet = Set.Make(SelSet) in
    let module SelSelCross = Cross2Sets (SelSet) (SelSet) (SelSetSet) in
    let inters = SelSelCross.cross intersect_sels s1 s2 in
    SelSetSet.fold SelSet.union inters SelSet.empty
  let intersections _ = SelSet.empty
  let union = SelSet.union
  let unions ss = List.fold_left union SelSet.empty ss
  let negate _ = SelSet.empty
  let subtract = SelSet.diff
  let singleton s = SelSet.add s SelSet.empty
  let singleton_string _ = None
  let var _ = SelSet.empty
  let pretty _ = "()"
  let is_empty _ = true
  let is_overlapped _ _ = true
  let is_subset _ _ _ = true
  let is_equal _ _ = true
  let example _ = None

    
  let pretty_sel s = FormatExt.text "(|dummy|)"
  let p_css t =
    if SelSet.cardinal t = 1
    then pretty_sel (SelSet.choose t)
    else SelSetExt.p_set pretty_sel t
end
