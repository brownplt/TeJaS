open Prelude
open Sig
open SetExt

module type CSS = sig
	include  SET
	type combinator = Css_syntax.combinator
	val concat_selectors : t -> combinator -> t -> t
	val p_css : t -> FormatExt.printer
	val targets : t -> Css_syntax.SimpleSelSet.t
	val speclist : t -> Css_syntax.spec list
	val sel2regsels : t -> Css_syntax.regsel list
	val regsel2sel : Css_syntax.regsel -> t
end

module RealCSS : CSS

module TestRealCSS : sig
	val testSels : int -> bool
end
