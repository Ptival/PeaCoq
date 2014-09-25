
var scrollbarWidth = 20; // arbitrary
var spacing = 20;
var accordionWidth = 200;

var menu =
    [
        {
            "title": "First steps",
            "items":
            [
                {
                    "name": "Booleans",
                    "onClick": firstStepsBooleans,
                },
                {
                    "name": "Natural numbers",
                    "onClick": function() { console.log("naturals"); },
                },
            ]
        },
        {
            "title": "Case analysis",
            "items":
            [
                {
                    "name": "Booleans",
                    "onClick": function() { console.log("booleans2"); },
                },
                {
                    "name": "Lists",
                    "onClick": function() { console.log("lists"); },
                },
            ]
        },
    ]
;

$(document).ready(function() {

    $("#accordion")
        .css("width", accordionWidth)
    ;

    $("#main")
        .css("width", $(window).width() - accordionWidth - scrollbarWidth - spacing)
        .css("margin-left", spacing + "px")
    ;

    populateMenu();

    setupTextareaResizing();

    syncQuery("Abort All.", function() { });

    // for faster debugging
    $("li > a").first().click();

});

function slugg(t) {
    var res =
        t
        .replace(/\s/g, '-')
        .toLowerCase()
    ;
    return res;
}

function populateMenu() {
    var group = $("#accordion");
    _(menu).each(function(e, ndx) {
        var title = e.title;
        var slug = slugg(title);
        var items = _(e.items).map(function(i) {
            return $("<li>")
                .append($('<a href="#">').text(i.name).click(function() {
                    var panel =
                        $("<div>")
                        .addClass("panel")
                        .addClass("panel-primary")
                    ;
                    panel.append(
                        $("<div>")
                            .addClass("panel-heading")
                            .html(
                                title
                                    + '&nbsp;<i class="glyphicon glyphicon-chevron-right"></i>&nbsp;'
                                    + i.name)
                    );
                    $("#main")
                        .empty()
                        .append(panel)
                    ;
                    var panelGroup = $("<ul>").addClass("list-group");
                    panel.append(panelGroup);
                    i.onClick(function(item) {
                        panelGroup.append(
                            $("<li>").addClass("list-group-item").append(item)
                        );
                    });
                }))
            ;
        });
        var panel = $("<div>")
            .addClass("panel")
            .html(
                '<div class="panel-heading">'
                    + '<a class="collapsed" data-toggle="collapse"'
                    + ' data-parent="#accordion" href="#' + slug + '">'
                    + '<h1 class="panel-title">'
                    + title
                    + '</h4></a></div>'
                    + '<div id="' + slug + '" class="panel-collapse collapse'
                    + (ndx == 0 ? ' in' : '')
                    + '">'
                    + '<div class="accordion-body">'
                    + '</div></div>'
            )
        ;
        group.append(panel);
        var itemContainer = panel.find(".accordion-body");
        _(items).each(function(i) {
            itemContainer.append(i);
        });
    });
}

function firstStepsBooleans(addItem) {

    addItem(
        $("<div>")
            .text("Here is our first Coq definition, the inductive type bool:")
    );

    addItem(mkClickableTextarea(inductiveBool, function() { }));

    addItem(
        $("<div>")
            .text("This one doesn't belong here, but testing is easier this way!")
    );

    addItem(mkClickableTextarea(inductiveNat, function() { }));

    $("textarea").change();
}

function setupTextareaResizing() {

    var minimalWidth = 10;
    var minimalHeight = 16;

    var hiddenDiv = $("<div id='invisible'>")
        .css("font-family", "monospace")
        .css("display", "none")
        .css("float", "right")
    ;

    $("body").append(hiddenDiv);

    var resizeTextarea = function() {
        content = $(this).val();
        hiddenDiv.html(
            content
                .replace(/\n/g, '&nbsp;&nbsp;<br>')
                .replace(/ /g, '&nbsp;')
                + '&nbsp;&nbsp;<br>'
                + '&nbsp;' // one more line to reduce jitter on newline
        );
        //$(this).css('width', Math.max(hiddenDiv.width() + minimalWidth, minimalWidth));
        $(this).css('height', Math.max(hiddenDiv.height(), minimalHeight));
    };

    $(document)
        .on('change keyup keydown paste', 'textarea', resizeTextarea)
    ;

}

function mkClickableTextarea(initialText) {
    var res = $("<div>").addClass("input-group");
    res.append(
        $("<span>")
            .addClass("input-group-btn")
            .append(mkPlayButton(function() {
                var li = $(this).parents("li").first();
                var text = li.find("textarea").val();
                syncParse(text, function(response) {
                    li.find("div.alert").remove();
                    li.append(
                        $("<div>")
                            .addClass("alert")
                            .addClass("alert-success")
                            .css("font-family", "monospace")
                            .html(showVernac(response))
                    );
                });
            }))
    );
    res.append(
        $("<textarea>")
            .addClass("form-control")
            .val(initialText)
    );
    return res;
}

function mkGlyph(name) {
    return $("<i>").addClass("glyphicon").addClass("glyphicon-" + name);
}

function mkPlayButton(onClick) {
    var res = $("<button>")
        .addClass("btn btn-default")
        .attr("type", "button")
        .append(mkGlyph("play"))
    ;
    res.click(onClick);
    return res;
}

var inductiveBool =
  'Inductive bool : Type :=\n'
+ '| true : bool\n'
+ '| false : bool\n'
+ '.'
;

var inductiveNat =
  'Inductive nat : Type :=\n'
+ '| O : nat\n'
+ '| S : nat -> nat\n'
+ '.'
;

function syncRequest(r, q, h) {
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: false,
        success: function(response) {
            h(response);
        }
    });
}

function syncQuery(q, h) { syncRequest('query', q, h); }

function syncQueryUndo(q, h) { syncRequest('queryundo', q, h); }

function syncParse(q, h) { syncRequest('parse', q, h); }
