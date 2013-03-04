/*::

type subt1 = #{ x : Num, y : Str }
type subt2 = #{ x : Num, y : Bool }
type supert = #{ x : Num }

*/

function f2(g, obj) /*: (supert -> Str) * supert -> Str */ {
  return g(obj);
}

function g2(obj) /*: subt1 -> Str */ {
  return obj.y + "foo";
}

f2(g2, { x : 5, y : true });

