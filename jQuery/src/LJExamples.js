
$(this);
eq(7),get(0),slice; // get is childrenOf + eq?

// Examples from Learning JQuery
// Chapter 2
// p41, Listing 2.10
$(document).ready(function() {
    $('td:contains(Henry)').next().addClass('highlight');
});

// p42, Listing 2.12
$(document).ready(function() {
    $('td:contains(Henry)').nextAll().andSelf()
	.addClass('highlight');
});


// p43, Listing 2.13
$(document).ready(function() {
    $('td:contains(Henry)').parent().children()
	.addClass('highlight');
});


// p43, Listing 2.15
$('td:contains(Henry)')     // Find every cell containing "Henry"
    .parent()               // Select its parent
    .find('td:eq(1)')       // Find the 2nd descendant cell
    .addClass('highlight')  // Add the "highlight" class
    .end()              // Return to the parent of the cell containing "Henry"
    .find('td:eq(2)')       // Find the 3rd descendant cell
    .addClass('highlight'); // Add the "highlight" class


// p229, Listing 9.2
// Unfinished code
$(document).ready(function() {
    $('#topics a').click(function() {
	var topic = $(this).text();
	$('#topics a.selected').removeClass('selected');
	$(this).addClass('selected');
	$('#news tr').show();
	if (topic != 'All') {
	    $('#news tr:has(td):not(:contains("' + topic + '"))')
                .hide();
        }
        return false;
    });
});


// p230, Listing 9.3
if (topic != 'All') {
    $('#news').find('tr:has(td)').not(function() {
        return $(this).children(':nth-child(4)').text() == topic;
    }).hide();
}


// p246, Listing 9.15
$(document).ready(function() {
  function stripe() {
    $('#news')
      .find('tr.alt').removeClass('alt').end()
      .find('tbody').each(function() {
        $(this).children(':visible').has('td')
          .filter(':group(3)').addClass('alt');
    });
  }
  stripe();
});



// Examples from blog of Learning JQuery and official JQuery website
$('li').eq(0);
$('li').not('.goofy');
$('ol .goofy > strong');
$('li + li > a[href$=pdf]');
$('span:hidden');


$('#jqdt2').find('li').siblings();
$('#jqdt2')
    .find('li.funny')
    .css('backgroundColor', '#0ff')
    .end()
    .find('p > strong')
    .css('backgroundColor', '#ff0');


$('li.goofy')
    .parents('#jqdt2')
    .children('p')
    .next()
    .find('a')
    .parent();



// Only example of add() in the book, not very friendly to the type checker
var colNum = $td[0].cellIndex + 1;
var $columnCells = $td
.closest('table')
.find('td, th')
.filter(':nth-child(' + colNum + ')');
$cells = $cells.add($columnCells);