/*:: (Tweet : """A structure for tweets"""
                   DivElement
                   optional classes = [first, last]
                   classes = [tweet]
                   (Author : DivElement classes = [author]
                      <Other>)
                   (Time : DivElement classes = [time] )
                   (Content : DivElement classes = [content] ... <Other> ...)
               )


type t0 = jQ<0<Tweet>, DefaultPrev>;
type t1 = jQ<1<Tweet>, AnyJQ>;
type t01 = jQ<01<Tweet>, DefaultPrev>;
type t1p = jQ<1+<Tweet>, DefaultPrev>;
type t0p = jQ<0+<Tweet>, DefaultPrev>;

*/

var t1 = /*: cheat t1 */0;
var t1p = /*: cheat t1p */0;

/*: jQ<1+<Author+Content+Time>, Any> */ t1.children();
/*: jQ<1+<Author>, Any> */t1.children().nextSib().nextSib().prevSib().prevSib();
/*: jQ<1+<Tweet+Author+Content+Time>, jQ<1+<Author+Content+Time>, Any>> */t1p.children().andSelf();


// /*: jQ<1+<Tweet+Author+Content+Time>, Any> */t1.children().andSelf();

t1.children().andSelf();



