/*::
(Tweet : """A structure for tweets"""
                   Div
                   optional classes = [first, last]
                   classes = [tweet]
                   (Author : Div classes = [author]
                      (Other : Div classes = [other])
                      <Other>)
                   (Time : Div classes = [time] )
                   (Content : Div classes = [content] ...)
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
/*: jQ<1+<Author>, Any> */t1.children().next().next().prev().prev();
/*: jQ<1+<Tweet+Author+Content+Time>, jQ<1+<Author+Content+Time>, Any>> */t1p.children().andSelf();


/*: jQ<1+<Tweet+Author+Content+Time>, Any> */t1.children().andSelf();

t1.children().andSelf();



