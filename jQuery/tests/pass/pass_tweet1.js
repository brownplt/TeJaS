
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
               )

type t0 = jQ<0<Tweet>, AnyJQ>;
type t1 = jQ<1<Tweet>, AnyJQ>;
type t01 = jQ<01<Tweet>, AnyJQ>;
type t0p = jQ<0+<Tweet>, AnyJQ>;
type t1p = jQ<1+<Tweet>, AnyJQ>;

type a1 = jQ<1<Author>, AnyJQ>;
type a1p = jQ<1+<Author>, AnyJQ>;

type c1 = jQ<1<Content>, AnyJQ>;

type o1 = jQ<1<Other>, AnyJQ>;

*/


var t0 = /*: cheat t0 */0;
var t1 = /*: cheat t1 */0;
var t01 = /*: cheat t01 */0;
var t0p = /*: cheat t0p */0;
var t1p = /*: cheat t1p */0;

var a1 = /*: cheat a1 */0;
var a1p = /*: cheat a1p */0;

var c1 = /*: cheat c1 */0;

var o1 = /*: cheat o1 */0;


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
var t1_children = t1.children();
/*: jQ<1+<Author+Content+Time>, AnyJQ> */t1_children;

// chained children
var t1_children2 = t1_children.children();
/*: jQ<1+<Followers>, AnyJQ> */t1_children2;


// children of something with no children is 0<Any>
/*: jQ<0<Any>, AnyJQ> */t1_children2.children();

// Children of 1 of something, when there is only one child, is one
var a1_children = a1.children();
/*: jQ<1<Follower>, AnyJQ> */a1_children;









// var tweet_element = /*: cheat JQ<1+<Tweet+Element>, AnyJQ> */0;

// tweet_element.children();
