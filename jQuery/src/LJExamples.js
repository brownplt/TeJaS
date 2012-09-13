// Examples from the book

// Source:
// Johnathan Chaffer, Karl Swedberg (2011), Learning JQuery (3rd ed.). Birmingham, UK: Packt Publishing Ltd.

// p41-41, Listing 2.10
$('td:contains(Henry)').next().addClass('highlight');

// p42-42, Listing 2.12
$('td:contains(Henry)').nextAll().andSelf()
    .addClass('highlight');


// p43-43, Listing 2.13
$('td:contains(Henry)').parent().children()
    .addClass('highlight');


// p43-44, Listing 2.15
$('td:contains(Henry)')     // Find every cell containing "Henry"
    .parent()               // Select its parent
    .find('td:eq(1)')       // Find the 2nd descendant cell
    .addClass('highlight')  // Add the "highlight" class
    .end()              // Return to the parent of the cell containing "Henry"
    .find('td:eq(2)')       // Find the 3rd descendant cell
    .addClass('highlight'); // Add the "highlight" class


// p229-229, Listing 9.2
$('#topics a').click(function() {
    var topic = $(this).text();
    $('#topics a.selected').removeClass('selected');
    $(this).addClass('selected');
    $('#news tr').show();
    if (topic != 'All') {
	$('#news tr:has(td):not(:contains("' + topic + '"))')
            .hide();
    }});


// p230-230, Listing 9.3
$('#news').find('tr:has(td)').not(function() {
    return $(this).children(':nth-child(4)').text() == topic;
}).hide();


// p246-246, Listing 9.15
$('#news')
    .find('tr.alt').removeClass('alt').end()
    .find('tbody').each(function() {
        $(this).children(':visible').has('td')
            .filter(':group(3)').addClass('alt');
    });


// Examples from blog of Learning JQuery

// Source:
// Karl Swedberg (2006), How to Get Anything You Want - part 1
// http://www.learningjquery.com/2006/11/how-to-get-anything-you-want-part-1

$('li').eq(0);
$('li').not('.goofy');
$('ol .goofy > strong');
$('li + li > a[href$=pdf]');
$('span:hidden');

// Source:
// Karl Swedberg (2006), How To Get Anything You Want - part 2
// http://www.learningjquery.com/2006/12/how-to-get-anything-you-want-part-2

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
