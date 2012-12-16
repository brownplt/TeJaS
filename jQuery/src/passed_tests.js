/*:: 

(Tweet : """A structure for tweets"""
                   div
                   // optional classes = [first, last]
                   classes = [tweet]
                   (Author : div classes = [author] ...)
                   (Time : div classes = [time] )
                   (Content : div classes = [content]
                              (Other : div classes = [other]))
                   <Content>
               )

// (Tweet2 : div
//           classes = [tweetalias]
//           <Content>)


type tw1 = jQ<1<Tweet>, jQ<1+<Element>, AnyJQ>>;
type tw2 = jQ<1+<Tweet>, AnyJQ>;
type a1 = jQ<1<Author>, AnyJQ>;
type a2 = jQ<1+<Author>, AnyJQ>;
type time1 = jQ<1<Time>, AnyJQ>;
type c1 = jQ<1<Content>, AnyJQ>;
type elem1 = jQ<1<Element>, AnyJQ>;
type elem2 = jQ<1+<Element>, AnyJQ>;
type top = jQ<1+<Any>, AnyJQ>;

*/

/** Simple Variable Definitions **/

// var f = /*: cheat (jQ<1+<Element>> -> jQ<1<Author>>) */0;
// var g = /*: cheat jQ<1<Time>> */0;
// var ret = /*: jQ<1+<Element>>*/(f(g));

var tw1 = /*: cheat tw1 */0;
var tw2 = /*: cheat tw2 */0;
var a1 = /*: cheat a1 */0;
var a2 = /*: cheat a2 */0;
var t1 = /*: cheat time1 */0;
var c1 = /*: cheat c1 */0;
var elem1 = /*: cheat elem1 */0;
var elem2 = /*: cheat elem2 */0;
// var other = /*: cheat other */0;
var anyJQ = /*: cheat top */0;


// /*: tw2 */$("div.tweet");
// /*: a2 */$("div.author.tag");
// /*: other */$("div.other");
// /*: jQ<0<Element>, AnyJQ> */$(".unknown.tweet");
// /*: jQ<0+<Element>, AnyJQ> */$("*+.tweet");
// /*: jQ<1+<Time>, AnyJQ>*/$(".tweet .author+.time");

// /*: jQ<0+<Element>, elem1> */elem1.parents();

// var triplePrevSib = /*: jQ<1+<Author+Time>, AnyJQ> */tw1.children().prevAll().prevSib().prevSib();



// var prev = /*: AnyJQ */tw1.end().end();
// var descendants = /*: jQ<1+<Element>, tw2> */tw2.find().addClass("highlight");
// var nextSibs = /*: jQ<1+<Time + Content>, a1> */a1.nextAll();
// var prevSibs = /*: jQ<1+<Author + Time>, c1> */c1.prevAll();
// var parents = /*: jQ<1+<Tweet + Content + Element>, other> */other.parents();
// var andSelf = /*: jQ<1+<Author + Time>, AnyJQ> */$(".author").nextSib().andSelf();
// var oneAuth = /*: jQ<1+<Author>, AnyJQ> */$(".author").nextSib().andSelf().end().end();
// var andSelf2 = tw1.andSelf();


// var doubleNextSibs = /*: jQ<0<Any>, Any> */a1.nextAll().nextAll().nextAll();
// /*: jQ<0<Any>, Any> */c1.next().next().next();
// var chain = /*: jQ<1+<Element + Other>, Any> */tw1.children().nextAll().prev().parent().children().children();

// The following tests all passed with the previous parameter being Any. Short chains passed with exact previous parameters. Long chains haven't been tested with exact previous parameters.
 
var simpleParent = /*: jQ<1+<Tweet>, a2> */(a2.parent());
// var simpleChildren = /*: jQ<1+<Content+Time+Author>, tw1> */(tw1.children());

// var longChain = /*: jQ<1+<Tweet>, Any> */(tw1.children().next().next().prev().prev().parent());
// var elementParent = /*: jQ<01<Element>, elem1> */(elem1.parent());

// var simplePrevSib = /*: jQ<1<Author>, time1> */(time1.prev());
// var tweet1PrevSib = /*: jQ<01<Element>, tw1> */(tw1.prev());
// var tweet2PrevSib = /*: jQ<0+<Element>, tw2> */(tw2.prev());
// var tweetNextSib = /*: jQ<01<Element>, tw1> */tw1.next();
// var tweetDoubleKids = /*: jQ<0+<Element>, jQ<1+<Content+Time+Author>, tw1>> */tw1.children().children();
// var tweetParent = /*: jQ<01<Element>, Any> */tw1.parent();

// var simpleNextSib = /*: jQ<1<Time>> */(a1.next());
// var parentOfAuthor = /*: cheat jQ<@parentOf<1+<Author>>, AnyJQ> */0;
// var parentOfAuthorCheck = /*: jq<1+<Author+Content+Time>> */parentOfAuthor.children();
// var otherNext = /*: jQ<1+<Element>, other> */other.next();


// /*: jQ<0+<Element>, AnyJQ> */a1.nextAll();

// The result of the following calls does not register the path through which we got to Content (the selector in TDom is *.content) 
// var content = /*: jQ<1+<Content>, AnyJQ> */tw1.children().filter(".content");

// /*: Num */tw1.children().next(); // .filter(".content")


