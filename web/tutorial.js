
var scrollbarWidth = 20; // arbitrary
var spacing = 20;
var accordionWidth = 200;
var currentTooltip = undefined;

function findTacticByName(tactics, name) {
    return _(tactics).find(function(x) { return x.name.indexOf(name) >= 0; });
}

function tag(tag, text) { return "<" + tag + ">" + text + "</" + tag + ">"; }
function p(text) { return tag("p", text); }
function code(text) { return tag("code", text); }

function ul(items) {
    return '<div class="panel panel-default"><ul class="list-group">'
        + items
        + '</ul></div>'
    ;
}

function li(text) {
    return '<li class="list-group-item">' + text + '</li>';
}

function mkText(t) { return $("<div>").html(t); }

function mkCoq(t, tactics, postAnim) {
    return mkClickableTextarea(t, tactics, postAnim);
}

function mkCoqReadonly(t, tactics, postAnim) {
    return mkReadonlyClickableTextarea(t, tactics, postAnim);
}

function drawTooltip(pt, node, arrowPosition, contents, onClick) {

    var arrowSize = 12;
    var tooltipMaxWidth = 400;

    pt.paused = true;
    // disable SVGPan
    enablePan  = 0;
    enableZoom = 0;

    /*
    var grayLayer = pt.tipsLayer
        .append("rect")
        .attr("width", pt.width)
        .attr("height", pt.height)
        .attr("x", - pt.viewportX)
        .attr("y", - pt.viewportY)
        .attr("fill", "gray")
        .attr("opacity", 0.2)
    ;
    */

    var fo = pt.tipsLayer
        .append("foreignObject")
        .attr("width", tooltipMaxWidth)
        .attr("height", 42)
    ;

    var body = fo
        .append("xhtml:body")
        .classed("svg", true)
        .style("background-color", "rgba(0, 0, 0, 0)")
        .html(
            '<div>'
                + '<div class="' + arrowPosition + '_arrow_box">'
                + contents
                + '</div>'
        )
        .on("click", function() {

            pt.paused = false;
            // enable SVGPan
            enablePan  = 1;
            enableZoom = 1;

            // clean up
            //grayLayer.remove();
            fo.remove();

            currentTooltip = undefined;

            onClick();

        })
    ;

    currentTooltip = body;

    $(body[0][0].children[0].children[0])
        .attr("position", "relative")
        .attr("z-index", 3)
    ;

    var bodyRect = body[0][0].children[0].children[0].getBoundingClientRect();

    switch(arrowPosition) {
    case "top":
        fo
            .attr("x", node.cX + node.width / 2 - bodyRect.width / 2)
            .attr("y", node.cY + node.height + arrowSize)
        ;
        break;
    case "right":
        fo
            .attr("x", node.cX - bodyRect.width - arrowSize)
            .attr("y", node.cY + node.height / 2 - bodyRect.height / 2)
        ;
        break;
    case "bottom":
        fo
            .attr("x", node.cX + node.width / 2 - bodyRect.width / 2)
            .attr("y", node.cY - bodyRect.height / 2 - arrowSize)
        ;
        break;
    case "left":
        fo
            .attr("x", node.cX + node.width + arrowSize)
            .attr("y", node.cY + node.height / 2 - bodyRect.height / 2)
        ;
        break;
    };

}

function tooltipSequence(pt, list) {
    if (_(list).isEmpty()) {
        return;
    } else {
        var head = _(list).first();
        var rest = _(list).rest();
        drawTooltip(pt, head.node, head.arrowPosition, head.contents, function() {
            tooltipSequence(pt, rest);
        });
    }
}

$(document).ready(function() {

    $("#accordion")
        .css("width", accordionWidth)
        .css("position", "fixed")
    ;

    $("#main")
        .css("width", $(window).width() - accordionWidth - scrollbarWidth - spacing)
        .css("margin-left", accordionWidth + spacing + "px")
    ;

    // artificially increase the document height to allow scrolling to the top of
    // any element
    $("body")
        .append(
            $("<div>")
                .css("height", $(window).height())
                .css("clear", "both")
                .css("float", "left")
                .html("&nbsp;")
        )
    ;

    populateMenu();

    PT.resetCoq();

    PT.handleKeyboard();

    $("body").on("keydown", function(event) {
        switch (event.keyCode) {
        case 13:
            if (currentTooltip !== undefined) {
                currentTooltip.on("click")();
                event.preventDefault();
                event.stopImmediatePropagation();
            }
            break;
        };
    });

    // for faster debugging
    $("li > a").first().click();
    $("button:first").focus();

    // scroll back to top once everything is laid out (arbitrary delay)
    window.setTimeout(function() { window.scrollTo(0, 0); }, 500);

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

    $.ajax({
        "async": false,
        "url": "first-steps.js",
        "datatype": "script"
    });

    var menu =
    [
        {
            "title": "PeaCoq tutorial",
            "items":
            [
                {
                    "name": "First steps",
                    "setup": firstSteps,
                },
            ]
        },
    ]
    ;

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

function clickableTextarea(readonly, initialText, tactics, postAnim) {
    var res = $("<div>").addClass("input-group");

    res.append(
        $("<textarea>")
            .addClass("form-control")
            .addClass("resizeHeight")
            .attr("readonly", readonly)
            .css("z-index", "0")
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

                    PT.syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            PT.syncParse(query, function(response) {
                                var answer =
                                    $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(showVernac(response))
                                ;
                                li.append(answer);
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
                        anchor.width(),
                        $(window).height(),
                        function(prooftree) { // qedCallback

                            var prettyTheorem;
                            PT.syncParse(prooftree.theorem, function(response) {
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

                            $("body").animate({
                                "scrollTop": li.children("div:nth(1)").offset().top,
                            }, 1000);

                            // focus on the next button, if any
                            li.nextAll().find("button").first().focus();

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

                    anchor.click(function() {
                        makeActive(pt);
                    });

                    pt.newTheorem(query,
                                  (tactics === undefined)
                                  ? function(pt) { return PT.tDiscriminate; }
                                  : tactics,
                                  (postAnim === undefined) ? function(){} : postAnim
                                 );

                } else if (query.startsWith("Definition")
                           || query.startsWith("Fixpoint")) {

                    PT.syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            PT.syncParse(query, function(response) {
                                var answer =
                                    $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(showVernac(response))
                                ;
                                li.append(answer);
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

                } else if (query.startsWith("Eval")) {

                    PT.syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            var response = stripWarning(response.rResponse.contents[0]);
                            PT.syncParseEval(response, function(response) {
                                var value = response[0];
                                var type = response[1];
                                li.append(
                                    $("<div>")
                                        .addClass("alert")
                                        .addClass("alert-success")
                                        .css("font-family", "monospace")
                                        .html(
                                            syntax("=") + nbsp + showTerm(value)
                                                + "<br>" + syntax(":") + nbsp + showTerm(type)
                                        )
                                );
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

                } else if (query.startsWith("Check")) {

                    PT.syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            var response = stripWarning(response.rResponse.contents[0]);
                            PT.syncParseCheck(response, function(response) {
                                var term = response[0];
                                var type = response[1];
                                li.append(
                                    $("<div>")
                                        .addClass("alert")
                                        .addClass("alert-success")
                                        .css("font-family", "monospace")
                                        .html(
                                            "<p>" + showTerm(term) + "</p>"
                                                + "<p>" + syntax(":") + nbsp + showTerm(type) + "</p>"
                                        )
                                );
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

                } else {

                    console.log("Query not supported", query);

                    PT.syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            var response = stripWarning(response.rResponse.contents[0]);
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(response)
                            );
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

                }

                $("body").animate({
                    "scrollTop": li.children("div:nth(1)").offset().top,
                }, 1000);

/*
                PT.syncParse(text, function(response) {
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

function mkReadonlyClickableTextarea(initialText, tactic, postAnim) {
    return clickableTextarea(true, initialText, tactic, postAnim);
}

function mkClickableTextarea(initialText, tactic, postAnim) {
    return clickableTextarea(false, initialText, tactic, postAnim);
}

function mkGlyph(name) {
    return $("<i>").addClass("glyphicon").addClass("glyphicon-" + name);
}

function mkPlayButton(onClick) {
    var res = $("<button>")
        .addClass("btn btn-default")
        .attr("type", "button")
        .addClass("svg") // keeps the focus on SVG on click
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

function stripWarning(s) { return s.substring(s.indexOf('\n') + 1); }

function nl2br (str) {
    return (str + '').replace(/([^>\r\n]?)(\r\n|\n\r|\r|\n)/g, '$1<br>$2');
}
