/*::

type subt1 = #{ x : Num, y : Str }
type supert = #{ x : Num }

*/

function f2(g, obj) /*: #(#(supert * Num -> Str) * supert -> Str) */ {
  return g(obj, 5);
}

function g2(obj) /*: #(subt1 -> Str) */ {
  return obj.y + "foo";
}

f2(g2, { x : 5, y : true });

