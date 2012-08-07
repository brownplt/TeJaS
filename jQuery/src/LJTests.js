/*::

(Plays : h2
         classes = [heading]);

(PlaysTable : """Shakespeare's plays"""
              table
              classes = [plays]
              (PlaysRow : tr
                          classes = [playsrow]
                          (PlayTitle : td classes = [title])
                          (PlayGenre : td classes = [genre])
                          (PlayYear : td classes = [year]))
              <PlaysRow>
              <PlaysRow>);

(Sonnets : h2
           classes = [heading]);

(SonnetsTable : table
                classes = [sonnets]
                (SonnetsRow : tr
                               classes = [sonnetsrow] 
                               (SonnetsTitle : td
                                               classes = [title])
                               (SonnetsLines : td
                                               classes = [lines]))
                <SonnetsRow>);

*/

/** (Simplified) Examples from Learning JQuery **/

// A few things that prevent us from typechecking $('td:contains(Henry)').next().addClass('highlight') :
// 1. We don't support pseudo-selectors yet (leave out :contains(Henry) for now)
// 3. If we leave out ':contains(Henry)', $('td').next() selects most of the cells in the structure, whereas in fact there should only be two cells  being selected.


$('td').next().addClass('highlight');

$('td').nextAll().andSelf().addClass('highlight');

$('td').parent().children().addClass('highlight');



// $('td')     // Find every cell containing "Henry"
//     .parent()               // Select its parent
//     .find()
//     .filter('td')
//     .eq(1)               // Find the 2nd descendant cell
//     .addClass('highlight')  // Add the "highlight" class
//     .end()
//     .end()
//     .end()              // Return to the parent of the cell containing "Henry"
//     .find()
//     .filter('td')
//     .eq(2)              // Find the 3rd descendant cell
//     .addClass('highlight'); // Add the "highlight" class
