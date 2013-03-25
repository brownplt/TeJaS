/* ::

// Shakespeare's plays and sonnets (for examples 1 and 5)

(Plays : h2
         classes = [heading]);

(PlaysTable : """Shakespeare's plays"""
              table
              ids = [playstable]
              classes = [plays]
              (PlaysRow : tr
                          classes = [playsrow]
                          (PlayTitle : td classes = [title] optional classes=[henry,highlight])
                          (PlayGenre : td classes = [genre] optional classes=[highlight])
                          (PlayYear : td classes = [year] optional classes=[highlight]))
              <PlaysRow>);
*/
/* ::
(Sonnets : h2
           classes = [heading]);

(SonnetsTable : table
                classes = [sonnets]
                (SonnetsRow : tr
                               classes = [sonnetsrow] 
                               (SonnetTitle : td
                                              classes = [title, test])
                               (SonnetLines : td
                                              classes = [lines, test]))
                <SonnetsRow>);
*/
/*::
// news (example 3)
(NewsTable : table
             classes = [news]
             ids = [news]
             (NewsHeader : thead
                           classes = [newsheader]
                           (HeaderRow : tr
                                        classes = [headerrow]
                                        (HeaderCell : th
                                                      classes = [headercell])
                                        <HeaderCell>))
             (NewsBody : tbody
                         classes = [newsbody]
                         (YearRow : tr
                                    classes = [yearrow])
                         (NewsRow : tr
                                    classes = [newsrow]
                                    optional classes = [alt] // XXX THIS WAS ADDED AND NEEDED!
                                    (NewsDate : td
                                                classes = [date])
                                    (NewTitle : td
                                                classes = [title])
                                    (NewAuthor : td
                                                 classes = [author])
                                    (NewTopic : td
                                                classes = [topic]))
                         <NewsRow>
                         <YearRow>
                         <NewsRow>
                         <NewsRow>))
*/
/* ::

// sample div (example 4 and 5)
(SampleDiv : div
             ids = [jqdt2]
             classes = [samplediv]
             (Paragraph : p
                          classes = [goofy]
                          (PChildStrong : strong
                                          classes = [pchildstrong]))
             (OrderedList : ol
                            classes = [list]
                            (LinkItem : li
                                        classes = [linkitem]
                                        (Link : a
                                                classes = [link]))
                            (GoofyItem : li
                                        classes = [goofy]
                                        (StrongText: strong
                                                     classes = [strongtext]))
                            (FunnyItem : li
                                        classes = [funny])
                            <LinkItem>
                            <GoofyItem>))


*/


// Examples from the book

// Source:
// Johnathan Chaffer, Karl Swedberg (2011), Learning JQuery (3rd ed.). Birmingham, UK: Packt Publishing Ltd.

// p41-41, Listing 2.10
// Example 1
// simple selector, simple type with horizontal local structure traversal
//$('td').next().addClass('highlight');

// p42-42, Listing 2.12
// Example 5
// simple selector, transitive traversal, jQuery stack
///*:Num*/$('td.henry').nextAll().andSelf();
//    .addClass('highlight');


// // p246-246, Listing 9.15
// // Example 3
// // assume each does not modify local structure
/*:Num*/$('#news')
    .find('tr.alt');
    // .removeClass('alt')
    // .end()
    // .find('tbody')
    // .each(function() {
    //     $(this).children(':visible').has('td')
    //         .addClass('alt');
    // });

// // Examples from blog of Learning JQuery

// // Source:
// // Karl Swedberg (2006)x, How To Get Anything You Want - part 2
// // http://www.learningjquery.com/2006/12/how-to-get-anything-you-want-part-2

// // Example 2
// $('#jqdt2')
//     .find('li.funny')
//     .css('backgroundColor', '#0ff')
//     .end()
//     .find('p > strong')
//     .css('backgroundColor', '#ff0');

// // Example 4


// $('li.goofy')
//     .parents('#jqdt2')
//     .children('p')
//     .next()
//     .find('a')
//     .parent();



// // // End selected examples





// // Source:
// // Karl Swedberg (2006), How to Get Anything You Want - part 1
// // http://www.learningjquery.com/2006/11/how-to-get-anything-you-want-part-1

// $('li').eq(0);
// // $('li').not('.goofy');

// // selector with structural information
// $('ol .goofy > strong');

// // // cannot deal with attributes in selectors
// // $('li + li > a[href$=pdf]');
// // $('span:hidden');


// // // HTGAYW2
// // // transitive
// // $('#jqdt2').find('li').siblings();

// // End HTGAYW


// // // p43-44, Listing 2.15
// // // chaining, stack
// // $('td')     // Find every cell containing "Henry"
// //     .parent()               // Select its parent
// //     .find('td').eq(1)       // Find the 2nd descendant cell
// //     .addClass('highlight')  // Add the "highlight" class
// //     .end().end()        // Return to the parent of the cell containing "Henry"
// //     .find('td').eq(2)       // Find the 3rd descendant cell
// //     .addClass('highlight'); // Add the "highlight" class



// // // p43-43, Listing 2.13
// // // simple selector, vertical traversal
// // $('td').parent().children()
// //     .addClass('highlight');


// // // p229-229, Listing 9.2
// // // selector with structural information
// // $('#topics a.selected').removeClass('selected');
// // // $('#news tr').show();



// // // p230-230, Listing 9.3
// // // not interesting for our purposes (no support for not() or user-defined function)
// // $('#news').find('tr:has(td)').not(function() {
// //     return $(this).children(':nth-child(4)').text() == topic;
// // }).hide();



// // // Only example of add() in the book, not very friendly to the type checker
// // var colNum = $td[0].cellIndex + 1;
// // var $columnCells = $td
// // .closest('table')
// // .find('td, th')
// // .filter(':nth-child(' + colNum + ')');
// // $cells = $cells.add($columnCells);

