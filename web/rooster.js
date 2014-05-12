
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
    $(textBlock).insertBefore($('#doit'));
    $('body').animate({
        scrollTop: $('#input').offset().top
    });
}

function addQuery(t) { addBlock(t, 'query'); }

function strOfGoal(g) {
    var res = '';
    _.forEach(g.gHyps, function(h) { res = res + h + '<br/>'; });
    res = res + '====================<br/>' + g.gGoal;
    return res;
}

function addResponse(response) {
    var r = response.coqtopResponse.contents[0];

    // remove this warning
    r = r.replace(/Warning: query commands should not be inserted in scripts/, '');

    r = r.replace(/^(\n)+/, ''); // remove newlines at the front
    r = r.replace(/(\n)+$/, ''); // remove newlines at the end
    r = str2html(r);

    addBlock(r, 'response');

    clearTabs();

    var currentGoal = response.currentGoals[0];
    if(currentGoal) {
        addBlock(strOfGoal(currentGoal), 'goal');

    var nbGoals = response.currentGoals.length;

    _.forEach(response.nextGoals, function(g, i){
        var tactic = g[0];
        var d = $('<div>');

        if(g[1].length < nbGoals) {
            d.append('SOLVED THE CURRENT GOAL!<br/><br/>');
        }

        _(g[1]).forEach(function(g){
            d.append(strOfGoal(g) + '<br/><br/>');
        });

        addTab('tab' + i, tactic, d.html());
    })

    }
}

function addTab(tabId, tabName, tabContent) {
    var li = $('<li><a href="#' + tabId + '">' + tabName + '</a></li>');
    var div = $('<div id="' + tabId + '">' + tabContent + '</div>');
    $('#tabs > ul').append(li);
    $('#tabs').append(div);
    $('#tabs').tabs('refresh');
    $('#tabs').tabs({
        activate: function(e, u) {
            $('#doit').off().on('click', function(){
                asyncQuery(u.newTab.text());
            });
        }
    });
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
