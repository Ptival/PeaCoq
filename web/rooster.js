
function str2html (str) {
    return (str + '')
    // nl2br
        .replace(/([^>\r\n]?)(\r\n|\n\r|\r|\n)/g, '$1<br/>$2')
    // protect the whitespaces
        .replace(/\s/g, '&nbsp;')
    ;
}

function syncQuery(s) {
    addQuery(s);
    $.ajax({ type: 'POST', url: 'query', data: {query : s}, async: false,
             success: function(response) { addResponse(response); } });
}

function asyncQuery(s) {
    addQuery(s);
    $.post('query', {query : s}, function(response) { addResponse(response); });
}

function addBlock(t, c) {
    var textBlock = $('<div>');
    $(textBlock).addClass(c);
    $(textBlock).html(t);
    $(textBlock).insertBefore($('#tabs'));
    $('body').animate({
        scrollTop: $('#input').offset().top
    });
}

function addQuery(t) { addBlock(t, 'query'); }

function addResponse(response) {
    var r = response.coqtopResponse.contents[0];

    // remove this warning
    r = r.replace(/Warning: query commands should not be inserted in scripts/, '');

    r = r.replace(/^(\n)+/, ''); // remove newlines at the front
    r = r.replace(/(\n)+$/, ''); // remove newlines at the end
    r = str2html(r);

    addBlock(r, 'response');

    var currentGoal = response.currentGoal[0];
    if(currentGoal) {
        var t = '';
        _.forEach(currentGoal.gHyps, function(h) { t = t + h + '<br/>'; });
        t = t + '====================<br/>' + currentGoal.gGoal;
        addBlock(t, 'goal');
    }

    clearTabs();
    _.forEach(response.nextGoals, function(g, i){
        var tactic = g[0];
        var d = $('<div>');

        _(g[1]).forEach(function(e){d.append('&nbsp;' + str2html(e) + '<br/><br/>');});

        var b = $('<button>', {
            text: 'DO IT!',
            id: 'submit' + i
        });

        $('#tabs').on('click', '#submit' + i, function(e){
            e.stopImmediatePropagation();
            asyncQuery(tactic);
        });

        $(d).append(b);
        addTab('tab' + i, tactic, d.html());
    })
}

function addTab(tabId, tabName, tabContent) {
    var li = $('<li><a href="#' + tabId + '">' + tabName + '</a></li>');
    var div = $('<div id="' + tabId + '">' + tabContent + '</div>');
    $('#tabs > ul').append(li);
    $('#tabs').append(div);
    $('#tabs').tabs('refresh');
}

function clearTabs() {
    $('#tabs > ul').empty();
    $('#tabs > div').remove();
}

function addTheorem(theorem) {
    var b = $('<button>', {
        text: theorem,
        click: function() {
            syncQuery('Abort All.');
            syncQuery(theorem);
        }
    });

    $('#theorems').append(b).append('<br/>');
}

$(document).ready(function() {

    $('#tabs').tabs();

    $('#form')
        .submit(function(e) {
            e.preventDefault();
            var q = $('#input').val();
            $('#input').val('');
            asyncQuery(q);
        })
    ;

    $('#input').focus();

    syncQuery('Show.');

    addTheorem('Theorem plus_comm : forall x y, x + y = y + x.');
    addTheorem('Theorem plus_assoc : forall x y z, (x + y) + z = x + (y + z).');

});
