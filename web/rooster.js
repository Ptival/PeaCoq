function nl2br (str) {
    return (str + '').replace(/([^>\r\n]?)(\r\n|\n\r|\r|\n)/g, '$1<br/>$2').replace(/\s/g, '&nbsp;');
}

function performQuery(s) {
    addQuery(s);

    $.ajax(
        { type: 'POST',
          url: 'query',
          data: {query : s},
          success: function(data) { addResponse(nl2br(data)); },
          async: false
        }
    );

/*
    $.post('query', {query : s}, function(data) {
        addResponse(nl2br(data));
    });
*/
}

function addBlock(t, c) {
    var textBlock = $('<div>');
    $(textBlock).addClass(c);
    $(textBlock).html(t);
    $(textBlock).insertBefore($('#form'));
    $('body').animate({
        scrollTop: $('#input').offset().top
    });
}

function addQuery(t) { addBlock(t, 'query'); }

function addResponse(t) { addBlock(t, 'response'); }

$(document).ready(function() {

    $('#form')
        .submit(function(e) {
            e.preventDefault();
            var q = $('#input').val();
            $('#input').val('');
            performQuery(q);
        })
    ;

    $('#input').focus();

    performQuery('Print plus.');

    performQuery('Print minus.');

    performQuery('Print ex.');

});
