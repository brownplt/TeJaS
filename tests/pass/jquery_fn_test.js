/*::

(A : div classes=[a]
   (B : div classes=[b] optional classes=[c])
   (D : div classes=[d]
     (E : div classes=[e] optional classes=[c]
       (F : div classes=[f])))
   <B>)


*/

/*: jQ<1+<A>, AnyJQ> */$(".a");

/*: jQ<1+<B>, AnyJQ> */$("div.a > div.b");

/*: jQ<1+<A>, AnyJQ> */$("p > div.a");

/*: jQ<1+<A>, AnyJQ> */$("p  div.a");

/*: jQ<1+<A>, AnyJQ> */$("p + div.a");

/*: jQ<1+<A>, AnyJQ> */$("p ~ div.a");

/*: jQ<0<Element>, AnyJQ> */$(".c > p > .a");

/*: jQ<Sum<1+<B>, 1+<E>>, AnyJQ> */$(".c");

/*: jQ<1+<F>, AnyJQ> */$(".f");

/*: jQ<1+<F>, AnyJQ> */$("div .f");

/*: jQ<1+<F>, AnyJQ> */$("div  div .f");

/*: jQ<1+<F>, AnyJQ> */$("div > div > div > .f");

/*: jQ<0<Element>, AnyJQ> */$("* + .f");

/*: jQ<0<Element>, AnyJQ> */$("div + .f");

/*: jQ<0<Element>, AnyJQ> */$("p + .f");

/*: jQ<1+<F>, AnyJQ> */$("p .f");

/*: jQ<0<Element>, AnyJQ> */$("p > .f");

/*: jQ<0<Element>, AnyJQ> */$(".bad + .f");

/*: jQ<1+<F>, AnyJQ> */$(".e > .f");

/*: jQ<0<Element>, AnyJQ> */$(".bad > div > div > div");

/*: jQ<0<Element>, AnyJQ> */$(".bad > div > div");

/*: jQ<1+<D>, AnyJQ> */$(".x > .y + .z ~ div.blah div div.d");

/*: jQ<Sum<1+<B>, 1+<D>>, AnyJQ> */$(".x > .y + .z ~ div.blah div.a > div");

/*: jQ<Sum<1+<B>, 1+<D>>, AnyJQ> */$(".x > .y + .z ~ div.blah div.a > *");

/*: jQ<Sum<1+<B>, Sum<1+<D>, Sum<1+<E>, 1+<F>>>>, AnyJQ> */$(".x > .y + .z ~ div.blah div.a *");

/*: jQ<0<Element>, AnyJQ> */$("p + .foo .bar .a > .b + .d .e > .bad");

/*: jQ<0<Element>, AnyJQ> */$(".f *");

/*: jQ<0<Element>, AnyJQ> */$("p .f div");

/*: jQ<0<Element>, AnyJQ> */$(".a > p + .b");

/*: jQ<1+<B>, AnyJQ> */$("div + .c");

/*: jQ<1+<B>, AnyJQ> */$(".b ~ .c");

// /*: jQ<1+<B>, AnyJQ> */$("* ~ .c"); // BUGBUG -- to be fixed

/*: jQ<1+<E>, AnyJQ> */$(".c.e");

/*: jQ<0<Element>, AnyJQ> */$(".div");

/*: jQ<1+<D>, AnyJQ> */$(".c + div");

/*: jQ<1+<B>, AnyJQ> */$("div.a > * + * + .b");

/*: jQ<0<Element>, AnyJQ> */$("div.a > * + * + * + .b"); 








