/*::

(Plays : h2
         classes = [heading]);

(PlaysTable : """Shakespeare's plays"""
              table
              classes = [plays]
              (PlaysRow : tr
                          classes = [playsrow]
                          (PlayTitle : td classes = [title, test])
                          (PlayGenre : td classes = [genre, test])
                          (PlayYear : td classes = [year, test]))
              <PlaysRow>);

(Sonnets : h2
           classes = [heading]);

(SonnetsTable : table
                classes = [sonnets]
                (SonnetsRow : tr
                               classes = [sonnetsrow] 
                               (SonnetsTitle : td
                                               classes = [title, test])
                               (SonnetsLines : td
                                               classes = [lines, test]))
                <SonnetsRow>);

*/

/** (Simplified) Examples from Learning JQuery **/

// A few things that prevent us from typechecking $('td:contains(Henry)').next().addClass('highlight') :
// 1. We don't support pseudo-selectors yet (leave out :contains(Henry) for now)
// 3. If we leave out ':contains(Henry)', $('td').next() selects most of the cells in the structure, whereas in fact there should only be two cells  being selected.

$('td.test').next().addClass('highlight');

$('td.test').nextAll().andSelf().addClass('highlight');

$('td.test').parent().children().addClass('highlight');


$('td.test')     // Find every cell containing "Henry"
    .parent()               // Select its parent
    .find()
    .filter('td')
    .eq(1)               // Find the 2nd descendant cell
    .addClass('highlight')  // Add the "highlight" class
    .end()
    .end()
    .end()              // Return to the parent of the cell containing "Henry"
    .find()
    .filter('td')
    .eq(2)              // Find the 3rd descendant cell
    .addClass('highlight'); // Add the "highlight" class
