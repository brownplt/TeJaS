
/*:: (Tweet : """A structure for tweets"""
                   Div
                   optional classes = [first, last]
                   classes = [tweet]
                   (Author : Div classes = [author]
                      (Other : Div classes=[other]))
                   (Time : Div classes = [time] )
                   (Content : Div classes = [content] ... )
               )


type t0 = jQ<0<Tweet>,DefaultPrev>;
type t1 = jQ<1<Tweet>,DefaultPrev>;
type t01 = jQ<01<Tweet>,DefaultPrev>;
type t1p = jQ<1+<Tweet>,DefaultPrev>;
type t0p = jQ<0+<Tweet>,DefaultPrev>;


*/

/* prev testing */


var t0 = /*: cheat t0 */0;
var t1 = /*: cheat t1 */0;
var t01 = /*: cheat t01 */0;
var t1p = /*: cheat t1p */0;
var t0p = /*: cheat t0p */0;


// /*: DefaultPrev */t0.end();
// /*: DefaultPrev */t1.end();
// /*: DefaultPrev */t01.end();
// /*: DefaultPrev */t1p.end();
// /*: DefaultPrev */t0p.end();


var i = t1.children().next().next();
/*: jQ<1+<Content+Time>,AnyJQ> */i.end();
/*: jQ<1+<Author+Content+Time>,AnyJQ> */i.end().end();
/*: t1 */i.end().end().end();



