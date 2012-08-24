/*::

(A : div classes=[a]
   (B : div classes=[b] optional classes=[c])
   (D : div classes=[d]
     (E : div classes=[e] optional classes=[c]
       (F : div classes=[f])))
   <B>)


*/

// PASS
// /*: Num */$(".a");

// PASS
// /*: Num */$("div.a > div.b");

// PASS
// /*: Num */$("p > div.a");

// PASS
// /*: Num */$("p  div.a");

// PASS
// /*: Num */$("p + div.a");

// PASS
// /*: Num */$("p ~ div.a");

// This is 0<Element>, because there can't be any local structure
// specs above local structure
// PASS
// /*: Num */$(".c > p > .a");

// I believe optional class intersection behavior needs to be changed
// PASS
// /*: Num */$(".c");

// PASS
// /*: Num */$(".f");

// PASS
// /*: Num */$("div .f");

// PASS
// /*: Num */$("div  div .f");

// PASS
// /*: Num */$("div > div > div > .f");

// Error parsing the selector annotation... this needs to be fixed?
// /*: Num */$(" * + .f");

// PASS
// /*: Num */$("div + .f");

// FAIL ( 1+<F> )
// /*: Num */$("p + .f");

// PASS
// /*: Num */$("p .f");

// PASS
// /*: Num */$("p > .f");

// FAIL ( 1+<F> )
/*: Num */$(".bad + .f");

// PASS
// /*: Num */$(".e > .f");

// PASS
// /*: Num */$(".bad > div > div > div");

// PASS
// /*: Num */$(".bad > div > div");

// PASS
// /*: Num */$(".x > .y + .z ~ div.blah div div.d");

// PASS
// /*: Num */$(".x > .y + .z ~ div.blah div.a > div");

// PASS
// /*: Num */$(".x > .y + .z ~ div.blah div.a > *");

// PASS
// /*: Num */$(".x > .y + .z ~ div.blah div.a  *");



