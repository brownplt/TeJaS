/*::

(A : div classes=[a]
   (B : div classes=[b] optional classes=[c])
   (D : div classes=[d]
     (E : div classes=[e] optional classes=[c]
       (F : div classes=[f])))
   <B>)


*/


// /*: Num */$(".a");
// /*: Num */$("div.a > div.b");

// /*: Num */$("p > div.a");

// /*: Num */$("p  div.a");

// /*: Num */$("p + div.a");

// /*: Num */$("p ~ div.a");

// This is 0<Element>, because there can't be any local structure
// specs above local structure
// /*: Num */$(".c > p > .a");


// I believe optional class intersection behavior needs to be changed
// /*: Num */$(".c");

// /*: Num */$(".f");

// /*: Num */$("div .f");

// /*: Num */$("div  div .f");

// /*: Num */$("div > div > div > .f");


// Error parsing the selector annotation... this needs to be fixed
// /*: Num */$(" * + .f");



// Look at what the intersection is here... I think the inter algo might be buggy.
// Result should be 0+<Element>, but is 1+<F>. I don't think the fn algo is wrong though.
// The intersection between the F selector and this selector is non-empty. It's
// the same as the F selector (obviously). Is this correct? Doesn't seem like it.

// /*: Num */$("div + .f");

// ***
// UPDATE: It actually seems like a parsing error. "p + .f" is being parsed into
// TWO selectors:  "*.f, p + *.f""/
//  ***
// That doesn't seem right.
// /*: Num */$("p + .f");


// // Same problem as above
// /*: Num */$("p .f");

// // Same problem as above
// /*: Num */$("p > .f");

// Interestingly, ".e + .f" is parsed correctly.
// But this breaks for the same reason as the .bad cases below
/*: Num */$(".bad + .f");

// This passes
// /*: Num */$(".e > .f");


// Weird edge-case that break down the algorithm
// /*: Num */$(".bad > div > div > div");

// /*: Num */$(".bad > div > div");

// The problem with the .bad cases above is that intersection works in a
// 'bottom-up' fashion and we need something that restricts in a 'top-down' fashion.
