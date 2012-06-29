open Prelude
open Sig
open SetExt

module type CSS = sig
  include  SET
  type combinator = Css_syntax.combinator
  val concat_selectors : t -> combinator -> t -> t
  val p_css : t -> FormatExt.printer
end

module RealCSS : CSS

module TestRealCSS : sig
  val testSels : int -> bool
end