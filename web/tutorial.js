
var scrollbarWidth = 20; // arbitrary
var spacing = 20;
var accordionWidth = 200;
var currentTooltip = undefined;


function findTacticByName(tactics, name) {
    return _(tactics).find(function(x) { return x.name.indexOf(name) >= 0; });
}

function p(text) { return "<p>" + text + "</p>"; }

function ul(text) {
    return '<div class="panel panel-default"><ul class="list-group">'
        + text
        + '</ul></div>'
    ;
}

function li(text) {
    return '<li class="list-group-item">' + text + '</li>';
}

function firstSteps(add) {

    add(mkText(
        "<p>Welcome to the world of the Coq proof assistant.</p>"
    ));

    add(mkText(
        p("In this lecture, we will use the following lexicon:")
            + ul(
                li(
                    "A <em>term</em> is any sequence of characters that makes sense in the language we will use to program and prove."
                ) + li (
                    "A <em>type</em> is a way to classify terms. Types can be empty (they don't contain any term), or have a finite or infinite number of terms."
                ) + li (
                    p(
                        "A <em>value</em> is a term obtained after performing all the possible computations."
                    ) + p(
                        "Every term is a value or can be computed down to a value."
                    ) + p(
                        "In particular, the type of a term will remain compatible with the type of its value. A <code>nat</code> (say, <code>2 + 3</code>) stays a <code>nat</code> (<code>5</code>)."
                    )
                )
            )
    ));

    add(mkText(
        "<p>One of the most basic types is the boolean type. A boolean value (a value of type <code>bool</code>) is either the constructor <code>true</code>, or the constructor <code>false</code>.</p><p>Click on the Play button below before you keep reading.</p>"
    ));

    add(mkCoqReadonly(
        "Inductive bool : Type := true | false."
    ));

    add(mkText(
        "<p>Once Coq has registered this new type, we print it again for checking purposes.</p><p>This text says that <code>bool</code> is a new inductive type (a value of type <code>Type</code>), and that there exists (only) two ways to build a value of type <code>bool</code>: one is the value <code>true</code>, and the other is the value <code>false</code>.</p><p>The meaning of <code>Inductive</code> will be explained later on.</p>"
    ));

    add(mkText(
        "<p>Let's prove something right away, a value of type <code>bool</code> can only be equal to <code>true</code> or equal to <code>false</code>.</p><p>Once again, and every time, click on the Play button and interact with the new window before continuing reading.</p>"
    ));

    add(mkCoqReadonly(
        'Theorem bools_are_true_or_false : forall b : bool, b = true \\\/ b = false.',
        function(pt) {
            if (pt.curNode.depth === 0) {
                return ["intro", "admit"];
            } else {
                return ["left", "right", "destruct", "reflexivity"];
            }
        },
        function(pt) {

            switch(pt.curNode.depth) {

            case 0:
                if (!pt.userState.introducedGoal) {
                    pt.userState.introducedGoal = true;
                    var introNode = findTacticByName(pt.curNode.children, "intro");
                    tooltipSequence(pt, [
                        {
                            "node": pt.curNode,
                            "arrowPosition": "left",
                            "contents":
                            "<p>This is your current goal. It is highlighted in green.</p>"
                                + '<p><code>∀</code> is a sign we use to mean "for all".</p>'
                                + '<p><code>b : bool</code> should be read as "b of type bool".</p>'
                                + '<p>Therefore, this goal asks you to prove that something is true '
                                + 'for any element <code>b</code> of the <code>bool</code> type.</p>'
                            ,
                        },
                        {
                            "node": introNode,
                            "arrowPosition": "top",
                            "contents":
                            "<p>This is a tactic node.</p>"
                                + "<p>In order to prove a goal, you will need to pick which tactic "
                                + "to run.</p>"
                                + "<p><code>intro</code> is the only tactic which applies here.</p>"
                                + "<p>It moves the universally-quantified variable <code>b</code> "
                                + "from your goal to your context.</p>"
                            ,
                        },
                        {
                            "node": introNode.children[0],
                            "arrowPosition": "right",
                            "contents":
                            "<p>This is the resulting subgoal.</p>"
                                + "<p>Everything above the horizontal line is your context.</p>"
                                + "<p>You can see the variable <code>b</code> of type "
                                + "<code>bool</code> has been moved from the goal to the "
                                + "context.</p>"
                                + "<p>You can hover your mouse over a subgoal to see what has "
                                + "changed from the previous goal. It's an easy way of checking "
                                + "what a tactic does.</p>"
                            ,
                        },
                    ]);
                }
                return;
                break;

            case 2:
                if (!pt.userState.introducedMultipleTactics) {
                    pt.userState.introducedMultipleTactics = true;
                    tooltipSequence(pt, [
                        {
                            "node": pt.curNode.children[2],
                            "arrowPosition": "top",
                            "contents":
                            "<p>There can be more than one tactic applicable to a given goal.</p><p>Some of them might do the wrong thing, so be mindful.</p>"
                            ,
                        },
                        {
                            "node": pt.curNode.parent,
                            "arrowPosition": "top",
                            "contents":
                            "<p>If you made a wrong move, you can always click on the parent tactic to go back up in the tree and change your decision.</p>"
                            ,
                        },
                        {
                            "node": findTacticByName(pt.curNode.children, "left"),
                            "arrowPosition": "top",
                            "contents":
                            "<p>The <code>left</code> tactic should be used when you think the left side of a disjunction is true. You will need to prove only that side if you pick this tactic.</p>"
                            ,
                        },
                        {
                            "node": findTacticByName(pt.curNode.children, "right"),
                            "arrowPosition": "top",
                            "contents":
                            "<p>The <code>right</code> tactic should be used when you think the right side of a disjunction is true.</p>"
                            ,
                        },
                        {
                            "node": findTacticByName(pt.curNode.children, "destruct b"),
                            "arrowPosition": "top",
                            "contents":
                            "<p>The <code>destruct</code> tactic lets you perform case-analysis on a value, according to its type. Here, it will split your goal into two subgoals, one for the case where <code>b</code> is <code>true</code>, and one for the case where <code>b</code> is <code>false</code>.</p>"
                            ,
                        },
                    ]);
                }
                return;
                break;

            };

            if (pt.curNode.allChildren.length === 0) {
                tooltipSequence(pt, [
                    {
                        "node": pt.curNode,
                        "arrowPosition": "top",
                        "contents":
                        "<p>No tactic applies to this goal!</p>"
                            + "<p>We can't solve it, it might be false!</p>"
                        ,
                    },
                    {
                        "node": pt.curNode.parent,
                        "arrowPosition": "top",
                        "contents":
                        "<p>Looks like you made a wrong decision.</p>"
                            + "<p>Click on this node to go back.</p>"
                        ,
                    },
                ]);
                return;
            }

            if (!pt.userState.introducedFinishingTactic
                && pt.curNode.allChildren.length === 1
                && pt.curNode.allChildren[0].allChildren.length === 0) {
                pt.userState.introducedFinishingTactic = true;
                tooltipSequence(pt, [
                    {
                        "node": pt.curNode.allChildren[0],
                        "arrowPosition": "right",
                        "contents":
                        "<p>This tactic does not have any subgoal.</p>"
                            + "<p>This means it solves the subgoal!</p>"
                            + "<p>Once you click on it, an animation will fold the "
                            + "things that have been proven.</p>"
                        ,
                    },
                ]);
                return;
            }

        }
    ));

    add(mkText(
        "<p>Once you are done with the proof, you should see the outline of the proof you just build. The Coq Proof Assistant registered the proof under the name <code>bools_are_true_or_false</code>.</p><p>The <code>Check</code> command lets you see the type of any value.</p>"
    ));

    add(mkCoqReadonly(
        "Check bools_are_true_or_false."
    ));

}

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
                        function(prooftree) {

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
                                var name = response[0];
                                var type = response[1];
                                li.append(
                                    $("<div>")
                                        .addClass("alert")
                                        .addClass("alert-success")
                                        .css("font-family", "monospace")
                                        .html(
                                            "<p>" + name + nbsp + syntax(":") + "</p>"
                                                + "<p>" + showTerm(type) + "</p>"
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
                    alert("This type of query is not supported yet.");
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
