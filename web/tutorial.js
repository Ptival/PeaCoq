
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
                    "setup": firstStepsBooleans,
                },
                {
                    "name": "Natural numbers",
                    "setup": function() { console.log("naturals"); },
                },
            ]
        },
        {
            "title": "Case analysis",
            "items":
            [
                {
                    "name": "Booleans",
                    "setup": function() { console.log("booleans2"); },
                },
                {
                    "name": "Lists",
                    "setup": function() { console.log("lists"); },
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

    resetCoq();

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

function mkPanel(title, item) {

    var panel =
        $("<div>")
        .addClass("panel")
        .addClass("panel-primary")
        .css("display", "none")
    ;

    panel.append(
        $("<div>")
            .addClass("panel-heading")
            .html(
                title
                    + nbsp
                    + mkGlyph("chevron-right").get(0).outerHTML
                    + nbsp
                    + item.name)
    );

    $("#main")
        .append(panel)
    ;

    var panelGroup = $("<ul>").addClass("list-group");

    panel.append(panelGroup);

    var buttonToAddLinesContainer =
        $("<li>")
        .addClass("list-group-item")
        .append(
            $("<button>")
                .addClass("label")
                .addClass("label-primary")
                .append(mkGlyph("plus"))
                .click(function() {
                    $(this).parent().before(
                        $("<li>")
                            .addClass("list-group-item")
                            .append(
                                mkClickableTextarea("")
                            )
                    );
                })
        )
    ;

    panelGroup.append(buttonToAddLinesContainer);

    item.setup(function(item) {
        buttonToAddLinesContainer.before(
            $("<li>").addClass("list-group-item").append(item)
        );
    });

    return panel;

}

function populateMenu() {
    var group = $("#accordion");
    _(menu).each(function(e, ndx) {
        var title = e.title;
        var slug = slugg(title);

        var items = _(e.items).map(function(i) {
            var thisPanel = mkPanel(title, i);
            return $("<li>")
                .append($('<a href="#">').text(i.name).click(function() {
                    $("#main > .panel").css("display", "none");
                    thisPanel.css("display", "");
                    $("textarea").change();
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
            .text("Here is a provable thingy:")
    );

    addItem(mkClickableTextarea(
        "Theorem trivial : forall b : bool, b = false \\/ b = true."
        , function() { }));

    addItem(
        $("<div>")
            .text("This one doesn't belong here, but testing is easier this way!")
    );

    addItem(mkClickableTextarea(inductiveNat, function() { }));

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
        $(this).css('height', Math.max(hiddenDiv.height() + 2, minimalHeight));
    };

    $(document)
        .on('change keyup keydown paste', 'textarea', resizeTextarea)
    ;

}

function mkClickableTextarea(initialText) {
    var res = $("<div>").addClass("input-group");
    res.append(
        $("<textarea>")
            .addClass("form-control")
            .val(initialText)
    );
    res.append(
        $("<span>")
            .addClass("input-group-btn")
            .append(mkPlayButton(function() {
                var li = $(this).parents("li").first();
                var query = li.find("textarea").val();

                // remove the previous alert, if any
                li.find("div.alert").remove();

                if (query.startsWith("Inductive")) {

                    syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            syncParse(query, function(response) {
                                var answer =
                                    $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(showVernac(response))
                                ;
                                li.append(answer);
                                $("body").animate({
                                        "scrollTop": li.offset().top,
                                }, 1000);
                            });
                            break;

                        case "Fail":
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-danger")
                                    .css("font-family", "monospace")
                                    .html(response.rResponse.contents)
                            );
                            break;

                        default:
                            alert("TODO");
                            break;

                        };

                    });

                } else if (query.startsWith("Theorem")) {

                    var anchor = $("<div>");

                    li.append(anchor);

                    var pt = new ProofTree(
                        d3.select(anchor.get(0)),
                        1330,
                        400,
                        function(prooftree) {

                            var prettyTheorem;
                            syncParse(prooftree.theorem, function(response) {
                                prettyTheorem = showVernac(response);
                            });

                            prooftree.replay();
                            prooftree.qed();
                            anchor.empty();
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(
                                        prettyTheorem
                                            + "<br>" + vernac("Proof") + syntax(".") + "<br>"
                                            + PT.pprint(prooftree.proof(), 1)
                                            + "<br>" + vernac("Qed") + syntax(".")
                                    )
                            );
                        },
                        undefined,
                        function(prooftree, error) {
                            prooftree.svg.style("display", "none");
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-danger")
                                    .css("font-family", "monospace")
                                    .html(error)
                            );
                        }
                    );

                    pt.newTheorem(query, PT.tDiscriminate, function() { }, function() { });

                } else {
                    alert("This type of query is not supported yet.");
                }

/*
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
*/

            }))
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

function currentLabel() {
    var result;
    syncRequest("status", "", function(response) {
        var msg = response.rResponse.contents[0];
        result = msg.match("^.*,.*,.*,\"(.*)\",.*$")[1];
    });
    return + result;
}

function resetCoq() {
    var label = currentLabel();
    if (label > 1) {
        syncRequest("rewind", label - 1, function() { });
        syncQuery("Require Import Unicode.Utf8.", function() { });
    }
}

if (!String.prototype.startsWith) {
  Object.defineProperty(String.prototype, 'startsWith', {
    enumerable: false,
    configurable: false,
    writable: false,
    value: function (searchString, position) {
      position = position || 0;
      return this.lastIndexOf(searchString, position) === position;
    }
  });
}
