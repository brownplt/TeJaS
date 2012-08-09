
/*:: 
(Other : div classes = [other])
(Tweet : """A structure for tweets"""
                   div
                   optional classes = [first, last]
                   classes = [tweet]
                   (Author : div classes = [author]
                     (Followers: div classes=[followers] optional classes = [hidden]))
                   (Time : div classes = [time] )
                   (Content : div classes = [content])
                   <Content>
               )

type t0 = jQ<0<Tweet>, AnyJQ>;
type t1 = jQ<1<Tweet>, AnyJQ>;
type t01 = jQ<01<Tweet>, AnyJQ>;
type t0p = jQ<0+<Tweet>, AnyJQ>;
type t1p = jQ<1+<Tweet>, AnyJQ>;

type a1 = jQ<1<Author>, AnyJQ>;
type a1p = jQ<1+<Author>, AnyJQ>;
 
type c1 = jQ<1<Content>, AnyJQ>;
type c1p = jQ<1+<Content>, AnyJQ>;

type o1 = jQ<1<Other>, AnyJQ>;

*/


// var t0 = /*: cheat t0 */0;
// var t1 = /*: cheat t1 */0;
// var t01 = /*: cheat t01 */0;
// var t0p = /*: cheat t0p */0;
// var t1p = /*: cheat t1p */0;

// var a1 = /*: cheat a1 */0;
// var a1p = /*: cheat a1p */0;

// var c1 = /*: cheat c1 */0;
// var c1p = /*: cheat c1p */0;

// var o1 = /*: cheat o1 */0;


/**** TId subtyping tests ****
* Several tests with TIds, as they can cause some weird edge-cases
****/

// /** Simple TId typing **/

// /*:: type Any2 = Any;
//      type Tweet2 = Tweet; */

// var any = /*: cheat Any */0;
// var any2 = /*: cheat Any2 */0;

// /*: Any */any2;
// /*: Any2 */any;
// /*: Any */any;
// /*: Any2 */any2;

// var tweet = /*: cheat Tweet */0;
// var tweet2 = /*: cheat Tweet2 */0;

// /*: Tweet */tweet2;
// /*: Tweet2 */tweet;

// /** Non-cheat TId **/
// // Make sure that TIds are getting resolved before association

// var tid_a1 = /*: a1 */a1;

// /*: jQ<1<Time>, AnyJQ> */tid_a1.next();
// /*: jQ<1<Time>, a1> */tid_a1.next();




/******************************************************************************/
/****----------- Broken tests that haven't been considered yet  -----------****/
/******************************************************************************/


/**** Children tests ****/

// TODO(liam): explore why resolve is being called on a type with @childrenOf<'n>

// 
var temp = /*:cheat jQ<1<Tweet>, AnyJQ>*/null;
/*:jQ<0+<Any>, AnyJQ>*/temp;

// var t1_children = t1.children();
// /*: jQ<1+<Author+Content+Time>, AnyJQ> */t1_children;

// // chained children
// var t1_children2 = t1_children.children();
// /*: jQ<1+<Followers>, AnyJQ> */t1_children2;


// // children of something with no children is 0<Any>
// /*: jQ<0<Any>, AnyJQ> */t1_children2.children();

// // Children of 1 of something, when there is only one child, is one
// var a1_children = a1.children();
// /*: jQ<1<Followers>, AnyJQ> */a1_children;

/**** END children tests ****/



// /**** Next, prev tests ****/

// // top-level next/prev
// /*: jQ<01<Element>, AnyJQ> */t1.next();
// /*: jQ<01<Element>, AnyJQ> */t1.prev();


// var a1_next = a1.next();
// var a1p_next = a1p.next();

// // single-author next
// /*: jQ<1<Time>, AnyJQ> */a1_next;

// // multi-author next
// /*: jQ<1+<Time>, AnyJQ> */a1p_next;

// var c1_next = c1.next();
// var cp1_next = c1p.next();

// // next for one content, which is the last child
// /*: jQ<01<Content>, AnyJQ> */c1_next;

// // next for more than one content
// /*: jQ<0+<Content>, AnyJQ> */cp1_next;


// var a1_prev = a1.prev();
// var a1p_prev = a1p.prev();

// // prev for author, which is first child 
// /*: jQ<0<Any>, AnyJQ> */a1_prev;

// // prev for more than one author
// /*: jQ<0<Any>, AnyJQ> */a1p_prev;

// // chaining next
// /*: jQ<1<Content>, AnyJQ> */a1.next().next();
// /*: jQ<1+<Num>, AnyJQ> */a1p.next().next();

// // chaining prev
// /*: jQ<1<Author+Time+Content>, AnyJQ> */c1.prev().prev();
// /*: jQ<1+<Author+Time+Content>, AnyJQ> */c1p.prev().prev();

// /*** END next, prev tests *****/


// var tweet_element = /*: cheat JQ<1+<Tweet+Element>, AnyJQ> */0;

// tweet_element.children();
