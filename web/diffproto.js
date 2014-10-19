
function avg(n1, n2) { return (n1 + n2) / 2; }

function mkDot(x, y) { return {"x": x, "y": y}; }

function showDot(d) { return d.x + " " + d.y; }

function midDot(d1, d2) { return mkDot(avg(d1.x, d2.x), avg(d1.y, d2.y)); }

function shiftLeft(d, n) { return mkDot(d.x - n, d.y); }
function shiftRight(d, n) { return mkDot(d.x + n, d.y); }

function connectRects(r1, r2, rightsLeft) {
    if (rightsLeft === undefined) { rightsLeft = r2.left; }
    var a = mkDot(r1.left, r1.top);
    var b = mkDot(r1.right, r1.top);
    var c = mkDot(rightsLeft, r2.top);
    var d = mkDot(r2.right, r2.top);
    var e = mkDot(r2.right, r2.bottom);
    var f = mkDot(rightsLeft, r2.bottom);
    var g = mkDot(r1.right, r1.bottom);
    var h = mkDot(r1.left, r1.bottom);

    var cp1 = mkDot(avg(b.x, c.x), b.y);
    var cp2 = mkDot(avg(f.x, g.x), c.y);
    var cp3 = mkDot(avg(f.x, g.x), f.y);
    var cp4 = mkDot(avg(f.x, g.x), g.y);

    return (
        "M" + showDot(a)
            + "L" + showDot(b)
            + "C" + showDot(cp1) + "," + showDot(cp2) + "," + showDot(c)
            + "L" + showDot(d) + "," + showDot(e) + "," + showDot(f)
            + "C" + showDot(cp3) + "," + showDot(cp4) + "," + showDot(g)
            + "L" + showDot(h)
            + "Z"
    );
}

function rectCenter(r) {
    return {"x": r.left + r.width / 2, "y": r.top + r.height / 2};
}

function rectCenterLeft(r) {
    return {"x": r.left, "y": r.top + r.height / 2};
}

function rectCenterRight(r) {
    return {"x": r.right, "y": r.top + r.height / 2};
}

function spotTheDifferences(before, after) {

    var removed = [];
    var added = [];

    function rec(before, after) {

        var nbBefore = before.children().length;
        var nbAfter  =  after.children().length;
        if (nbBefore !== nbAfter) {
            removed.push(before);
            added.push(after);
            return;
        }

        var nbChildren = nbBefore;
        if (nbChildren === 0) { // both leaves
            if (before.html() !== after.html()) {
                removed.push(before);
                added.push(after);
            }
            return;
        }

        for (var i in _.range(nbChildren)) {
            rec($(before.children()[i]), $(after.children()[i]));
        }

    }

    rec($(before), $(after));

    return {"removed": removed, "added": added};
}

var width = 1580;
var height = 820;
var nodeWidth = 600;

var red   = "#DD9999";
var green = "#99DD99";
var blue  = "#9999DD";
var redStroke   = red;
var greenStroke = green;
var blueStroke  = blue;
var strokeWidth = 2;
var opacity = 1;

function nodeX(d) {
    if (isGoal(d)) {
        return d.y * (width - nodeWidth);
    } else {
        return d.y * (width - nodeWidth) + (nodeWidth - d.rect.width) / 2;
    }
}

function nodeY(d) {
    return d.x * height - d.rect.height / 2;
}

function isGoal(n) { return (n.depth % 2 === 0); }

function isTactic(n) { return (n.depth % 2 === 1); }

$(document).ready(function() {

    var svg = d3.select("body").append("svg")
        .attr("width", width)
        .attr("height", height)
    ;

    var linkLayer = svg.append("g");
    var rectLayer = svg.append("g");
    var diffLayer = svg.append("g");
    var textLayer = svg.append("g");

    var tree = d3.layout.tree()
        .children(function(d) {
            return d.allChildren;
        })
    ;

    var nodes = tree.nodes(rootNode);
    var links = tree.links(nodes);
    var diagonal = d3.svg
        .diagonal()
        .projection(function(d) { return [d.y, d.x]; })
    ;

// first do the foreignObject, as the other things will position themselves accordingly

    var textSelection = textLayer
        .selectAll(function() {
            return this.getElementsByTagName("foreignObject");
        })
        .data(nodes)
    ;

    textSelection.enter()
        .append("foreignObject")
        .attr("width", nodeWidth)
        .append("xhtml:body")
        .style("padding", "4px")
        .style("background-color", "rgba(0, 0, 0, 0)")
        .each(function(d) {
            var jqObject = $(d3.select(this).node());
            var jQContents;
            if (isTactic(d)) {
                d.span = $("<span>").addClass("tacticNode").css("padding", "4px").text(d.pName);
                jQContents = d.span;
            } else {
                jQContents = $("<div>").addClass("goalNode");
                _(d.hyps).each(function(h) {
                    h.div = $("<div>").html(PT.showHypothesis(h))[0];
                    jQContents.append(h.div);
                });
                jQContents.append($("<hr>"));
                d.goalSpan = $("<span>").html(showTerm(d.name));
                jQContents.append(d.goalSpan);
            }
            jqObject.append(jQContents);
        })
        .on("mouseover", function(d1) {
            diffLayer.selectAll("g")
                .filter(function(d2) { return d1.id === d2.id; })
                .style("opacity", 1);
        })
        .on("mouseout", function(d1) {
            diffLayer.selectAll("g")
                .filter(function(d2) { return d1.id === d2.id; })
                .style("opacity", 0);
        })
    ;

    textSelection
        .attr("height", function(d) {
            return this.firstChild.getBoundingClientRect().height;
        })
        .each(function(d) {
            var jQElementToMeasure =
                isTactic(d)
                ? $(d3.select(this).node()).children(0).children(0) // get the span
                : $(d3.select(this).node()) // get the foreignObject itself
            ;
            d.rect = jQElementToMeasure[0].getBoundingClientRect();
        })
        .attr("x", nodeX)
        .attr("y", nodeY)
        .each(function(d) {
            var jQElementToMeasure =
                isTactic(d)
                ? $(d3.select(this).node()).children(0).children(0) // get the span
                : $(d3.select(this).node()) // get the foreignObject itself
            ;
            d.rect = jQElementToMeasure[0].getBoundingClientRect();
        })
    ;

    var rectSelection = rectLayer.selectAll("rect").data(nodes);

    rectSelection.enter()
        .append("rect")
        .classed("goal", isGoal)
        .classed("tactic", isTactic)
        .attr("width", function(d) { return d.rect.width; })
        .attr("height", function(d) { return d.rect.height; })
        .attr("x", function(d) { return d.rect.left; })
        .attr("y", function(d) { return d.rect.top; })
        .attr("rx", function(d) { return isTactic(d) ? 10 : 0; })
    ;

    var diffSelection = diffLayer.selectAll("g").data(nodes);

    diffSelection.enter()
        .append("g")
        .each(function(d) {
            if (hasGrandParent(d)) {
                var gp = d.parent.parent;
                var oldHyps = gp.hyps.slice();
                var newHyps = d.hyps.slice();
                var rightY = d.rect.top;
                var leftY = gp.rect.top;

                var delta = 1;
                function emptyRectLeft() {
                    return $.extend(
                        {},
                        gp.rect,
                        {"top": leftY - delta, "bottom": leftY + delta, "height": 2 * delta}
                    );
                }
                function emptyRectRight() {
                    return $.extend(
                        {},
                        d.rect,
                        {"top": rightY - delta, "bottom": rightY + delta, "height": 2 * delta}
                    );
                }

                function hypRect(h) { return h.div.getBoundingClientRect(); }
                function tacLeft(n) { return n.span[0].getBoundingClientRect().left; }

                var removed = [];
                var added = [];
                var changed = [];

                _(oldHyps).each(function(h) {
                    var match = _(newHyps).find(function(g) { return g.hName === h.hName; });
                    if (match !== undefined) {
                        changed.push({"before": h, "after": match});
                    } else {
                        removed.push(h);
                    }
                });
                _(newHyps).each(function(h) {
                    var match = _(oldHyps).find(function(g) { return g.hName === h.hName; });
                    if (match === undefined) { added.push(h); }
                });

                var d3this = d3.select(this);
                while (oldHyps.length !== 0 && newHyps.length !== 0) {
                    var oldChanged = _(changed).some(function(c) {
                        return c.before.hName === oldHyps[0].hName;
                    });
                    var newChanged = _(changed).some(function(c) {
                        return c.after.hName === newHyps[0].hName;
                    });
                    if (oldChanged && newChanged) {
                        var oldHyp = oldHyps.shift(), newHyp = newHyps.shift();
                        if (JSON.stringify(oldHyp.hType) !== JSON.stringify(newHyp.hType)) {
                            d3this
                                .append("path")
                                .attr("fill", blue)
                                .attr("stroke", blueStroke)
                                .attr("stroke-width", strokeWidth)
                                .attr("opacity", opacity)
                                .attr("d", connectRects(hypRect(oldHyp),
                                                        hypRect(newHyp),
                                                        tacLeft(d.parent)))
                            ;

                            var diff = spotTheDifferences(oldHyp.div, newHyp.div);

                            _(diff.removed).each(function(d) {
                                var rect = d[0].getBoundingClientRect();
                                d3this
                                    .append("rect")
                                    .attr("fill", red)
                                    .attr("x", rect.left)
                                    .attr("width", rect.width)
                                    .attr("y", rect.top)
                                    .attr("height", rect.height)
                                ;
                            });

                            _(diff.added).each(function(d) {
                                var rect = d[0].getBoundingClientRect();
                                d3this
                                    .append("rect")
                                    .attr("fill", green)
                                    .attr("x", rect.left)
                                    .attr("width", rect.width)
                                    .attr("y", rect.top)
                                    .attr("height", rect.height)
                                ;
                            });

                        }

                        leftY = hypRect(oldHyp).bottom;
                        rightY = hypRect(newHyp).bottom;
                    } else if (oldChanged) {
                        var newHyp = newHyps.shift();
                        d3this
                            .append("path")
                            .attr("fill", green)
                            .attr("stroke", greenStroke)
                            .attr("stroke-width", strokeWidth)
                            .attr("opacity", opacity)
                            .attr("d", connectRects(emptyRectLeft(),
                                                    hypRect(newHyp),
                                                    tacLeft(d.parent)))
                        ;
                        rightY = hypRect(newHyp).bottom;
                    } else if (newChanged) {
                        var oldHyp = oldHyps.shift();
                        d3this
                            .append("path")
                            .attr("fill", red)
                            .attr("stroke", redStroke)
                            .attr("stroke-width", strokeWidth)
                            .attr("opacity", opacity)
                            .attr("d", connectRects(hypRect(oldHyp),
                                                    emptyRectRight(),
                                                    tacLeft(d.parent)))
                        ;
                        leftY = hypRect(oldHyp).bottom;
                    } else {
                        var oldHyp = oldHyps.shift();

                        d3this
                            .append("path")
                            .attr("fill", red)
                            .attr("stroke", redStroke)
                            .attr("stroke-width", strokeWidth)
                            .attr("opacity", opacity)
                            .attr("d", connectRects(hypRect(oldHyp),
                                                    emptyRectRight(),
                                                    tacLeft(d.parent)))
                        ;

                        leftY = hypRect(oldHyp).bottom;
                    }
                }

                _(oldHyps).each(function(oldHyp) {
                    d3this
                        .append("path")
                        .attr("fill", red)
                        .attr("stroke", redStroke)
                        .attr("stroke-width", strokeWidth)
                        .attr("opacity", opacity)
                        .attr("d", connectRects(hypRect(oldHyp),
                                                emptyRectRight(),
                                                tacLeft(d.parent)))
                    ;
                });

                _(newHyps).each(function(newHyp) {
                    d3this
                        .append("path")
                        .attr("fill", green)
                        .attr("stroke", greenStroke)
                        .attr("stroke-width", strokeWidth)
                        .attr("opacity", opacity)
                        .attr("d", connectRects(emptyRectLeft(),
                                                hypRect(newHyp),
                                                tacLeft(d.parent)))
                    ;
                });

                var diff = spotTheDifferences(gp.goalSpan, d.goalSpan);

                _(diff.removed).each(function(d) {
                    var rect = d[0].getBoundingClientRect();
                    d3this
                        .append("rect")
                        .attr("fill", red)
                        .attr("x", rect.left)
                        .attr("width", rect.width)
                        .attr("y", rect.top)
                        .attr("height", rect.height)
                    ;
                });

                _(diff.added).each(function(d) {
                    var rect = d[0].getBoundingClientRect();
                    d3this
                        .append("rect")
                        .attr("fill", green)
                        .attr("x", rect.left)
                        .attr("width", rect.width)
                        .attr("y", rect.top)
                        .attr("height", rect.height)
                    ;
                });

            }

        })
        .style("opacity", 0)
    ;

    var linkSelection = linkLayer.selectAll("path").data(links);

    linkSelection.enter()
        .append("path")
        .classed("link", true)
        .attr("d", function(d) {
            function flip(r) { return {"x": r.y, "y": r.x}; }
            var src = flip(rectCenterRight(d.source.rect));
            var tgt = flip(rectCenterLeft(d.target.rect));
            return diagonal({"source": src, "target": tgt});
        })
    ;

});

var rootNode1 =
{"id":"133","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"b"}]},"pName":"Eq = b","depth":4,"hyps":[{"hName":"b","hType":{"tag":"Var","contents":"comparison"},"hValue":null},{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null}],"allChildren":[{"id":"176","name":"rewrite -> H0.","pName":"rewrite -> H0.","depth":5,"allChildren":[{"id":"177","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"pName":"Eq = Eq","depth":6,"hyps":[{"hName":"b","hType":{"tag":"Var","contents":"comparison"},"hValue":null},{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"178","name":"rewrite <- H0.","pName":"rewrite <- H0.","depth":5,"allChildren":[{"id":"179","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"b"}]},"pName":"b = b","depth":6,"hyps":[{"hName":"b","hType":{"tag":"Var","contents":"comparison"},"hValue":null},{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"184","name":"destruct H.","pName":"destruct H.","depth":5,"allChildren":[{"id":"185","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"c"}]},{"tag":"Var","contents":"b"}]},"pName":"c = b","depth":6,"hyps":[{"hName":"b","hType":{"tag":"Var","contents":"comparison"},"hValue":null},{"hName":"c","hType":{"tag":"Var","contents":"comparison"},"hValue":{"tag":"Var","contents":"Eq"}},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"c"}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"186","name":"destruct H0.","pName":"destruct H0.","depth":5,"allChildren":[{"id":"187","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"b"}]},"pName":"b = b","depth":6,"hyps":[{"hName":"b","hType":{"tag":"Var","contents":"comparison"},"hValue":null},{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"b"}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"202","name":"inversion H0.","pName":"inversion H0.","depth":5,"allChildren":[{"id":"203","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"pName":"Eq = Eq","depth":6,"hyps":[{"hName":"b","hType":{"tag":"Var","contents":"comparison"},"hValue":null},{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H1","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"b"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"180","name":"destruct b.","pName":"destruct b.","depth":5,"allChildren":[{"id":"181","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"pName":"Eq = Eq","depth":6,"hyps":[{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null}],"allChildren":[]},{"id":"182","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Lt"}]},"pName":"Eq = Lt","depth":6,"hyps":[{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Lt"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null}],"allChildren":[]},{"id":"183","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Gt"}]},"pName":"Eq = Gt","depth":6,"hyps":[{"hName":"H","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Eq"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null},{"hName":"H0","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"Gt"}]},{"tag":"Var","contents":"Eq"}]},"hValue":null}],"allChildren":[]}],"terminating":false}]};

var rootNode2 =
{"id":"88","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]},{"tag":"Var","contents":"0"}]}]},"pName":"0 + S m = S m + 0","depth":8,"hyps":[{"hName":"m","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHm","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]},"hValue":null}],"allChildren":[{"id":"100","name":"simpl.","pName":"simpl.","depth":9,"allChildren":[{"id":"101","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]}]},"pName":"S m = S (m + 0)","depth":10,"hyps":[{"hName":"m","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHm","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"102","name":"simpl in *.","pName":"simpl in *.","depth":9,"allChildren":[{"id":"103","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]}]},"pName":"S m = S (m + 0)","depth":10,"hyps":[{"hName":"m","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHm","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"109","name":"destruct IHm.","pName":"destruct IHm.","depth":9,"allChildren":[{"id":"110","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]},{"tag":"Var","contents":"0"}]}]},"pName":"0 + S m = S m + 0","depth":10,"hyps":[{"hName":"m","hType":{"tag":"Var","contents":"nat"},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"106","name":"destruct m.","pName":"destruct m.","depth":9,"allChildren":[{"id":"107","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"1"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"1"}]},{"tag":"Var","contents":"0"}]}]},"pName":"0 + 1 = 1 + 0","depth":10,"hyps":[{"hName":"IHm","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"0"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"0"}]}]},"hValue":null}],"allChildren":[]},{"id":"108","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]},{"tag":"Var","contents":"0"}]}]},"pName":"0 + S (S m) = S (S m) + 0","depth":10,"hyps":[{"hName":"m","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHm","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]},{"tag":"Var","contents":"0"}]}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"111","name":"induction m.","pName":"induction m.","depth":9,"allChildren":[{"id":"112","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"1"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"1"}]},{"tag":"Var","contents":"0"}]}]},"pName":"0 + 1 = 1 + 0","depth":10,"hyps":[{"hName":"IHm","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"0"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"0"}]}]},"hValue":null}],"allChildren":[]},{"id":"113","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]},{"tag":"Var","contents":"0"}]}]},"pName":"0 + S (S m) = S (S m) + 0","depth":10,"hyps":[{"hName":"m","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHm","hType":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]},{"tag":"Var","contents":"0"}]}]},"hValue":null},{"hName":"IHm0","hType":{"tag":"Arrow","contents":[{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"m"}]}]},{"tag":"Var","contents":"0"}]}]}]},"hValue":null}],"allChildren":[]}],"terminating":false}]};

var rootNode3 =
{"id":"59","name":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]}]},"pName":"∀ m : nat, S n + m = m + S n","depth":4,"hyps":[{"hName":"n","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHn","hType":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"n"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"n"}]}]}]},"hValue":null}],"allChildren":[{"id":"176","name":"simpl.","pName":"simpl.","depth":5,"allChildren":[{"id":"177","name":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"n"}]},{"tag":"Var","contents":"m"}]}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]}]},"pName":"∀ m : nat, S (n + m) = m + S n","depth":6,"hyps":[{"hName":"n","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHn","hType":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"n"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"n"}]}]}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"180","name":"intro.","pName":"intro.","depth":5,"allChildren":[{"id":"181","name":{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]},"pName":"S n + m = m + S n","depth":6,"hyps":[{"hName":"n","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHn","hType":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"n"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"n"}]}]}]},"hValue":null},{"hName":"m","hType":{"tag":"Var","contents":"nat"},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"184","name":"destruct n.","pName":"destruct n.","depth":5,"allChildren":[{"id":"185","name":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"1"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"1"}]}]}]},"pName":"∀ m : nat, 1 + m = m + 1","depth":6,"hyps":[{"hName":"IHn","hType":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]}]},"hValue":null}],"allChildren":[]},{"id":"186","name":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]}]}]},"pName":"∀ m : nat, S (S n) + m = m + S (S n)","depth":6,"hyps":[{"hName":"n","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHn","hType":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]}]},"hValue":null}],"allChildren":[]}],"terminating":false},{"id":"187","name":"induction n.","pName":"induction n.","depth":5,"allChildren":[{"id":"188","name":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"1"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"1"}]}]}]},"pName":"∀ m : nat, 1 + m = m + 1","depth":6,"hyps":[{"hName":"IHn","hType":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"0"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"0"}]}]}]},"hValue":null}],"allChildren":[]},{"id":"189","name":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]}]}]},"pName":"∀ m : nat, S (S n) + m = m + S (S n)","depth":6,"hyps":[{"hName":"n","hType":{"tag":"Var","contents":"nat"},"hValue":null},{"hName":"IHn","hType":{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]}]},"hValue":null},{"hName":"IHn0","hType":{"tag":"Arrow","contents":[{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"n"}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"Var","contents":"n"}]}]}]},{"tag":"Forall","contents":[[[["m"],{"tag":"Var","contents":"nat"}]],{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"eq"},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]},{"tag":"Var","contents":"m"}]}]},{"tag":"App","contents":[{"tag":"App","contents":[{"tag":"Var","contents":"plus"},{"tag":"Var","contents":"m"}]},{"tag":"App","contents":[{"tag":"Var","contents":"S"},{"tag":"Var","contents":"n"}]}]}]}]}]},"hValue":null}],"allChildren":[]}],"terminating":false}]};
