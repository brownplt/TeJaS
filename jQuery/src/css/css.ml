open Prelude
open Sig
open SetExt

module type CSS = sig
  include  SET

  val concat_selectors : t -> t -> t
  val p_css : t -> FormatExt.printer
end

module DummyCSS : CSS = struct
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

  let concat_selectors _ _ = SelSet.empty
  let pretty_sel s = FormatExt.text "(|dummy|)"
  let p_css t = 
    if SelSet.cardinal t = 1 
    then pretty_sel (SelSet.choose t)
    else SelSetExt.p_set pretty_sel t
end
