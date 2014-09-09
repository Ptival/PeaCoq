
"use strict";

/*
  Note: in strict mode, eval does not populate the global namespace with global
  scope variables.
  Therefore $.getScript will not see the global variables unless they are attached
  to window manually.
  Since I like strict mode, things to be exported have to be registered in the PT
  namespace.
*/
window.PT = {};

// CONFIGURATION
var nodeMinSpacing = 5;
var nodeStroke = 2;
var rectMargin = {top: 2, right: 8, bottom: 2, left: 8};
var nbChildrenToShow = 2;
var animationDuration = 420;

// COMPUTED GLOBALS
var activeProofTree = undefined;
var maxNodesOnLine = Math.pow(nbChildrenToShow, 2);
var diagonal = d3.svg.diagonal();

// These tactic sets each build on top of the previous one
PT.tSet = ['simpl', 'simpl in *', 'reflexivity', 'intro', 'rewrite', 'destruct', 'induction'];
PT.tReflexivity = PT.tSet.slice(0, 1 + PT.tSet.indexOf('reflexivity'));
PT.tIntro       = PT.tSet.slice(0, 1 + PT.tSet.indexOf('intro'));
PT.tRewrite     = PT.tSet.slice(0, 1 + PT.tSet.indexOf('rewrite'));
PT.tDestruct    = PT.tSet.slice(0, 1 + PT.tSet.indexOf('destruct'));
PT.tInduction   = PT.tSet.slice(0, 1 + PT.tSet.indexOf('induction'));
// These ones are more specific
PT.tCompute = PT.tReflexivity.concat(['compute']);

// [width] and [height] are the wanted ones, it might end up slightly smaller
function ProofTree(anchor, width, height, qed, roosterDir) {

    var self = this;

    this.anchor = anchor;
    this.qedCallback = qed;
    this.roosterDir = (typeof roosterDir === "undefined") ? "./" : roosterDir + "/";

    this.svgId = _.uniqueId();

    this.animationRunning = false;

    this.smallestNodeWidth = evenFloor(
        (width
         - ((maxNodesOnLine - 1) * nodeMinSpacing)
        ) / maxNodesOnLine
    );

    this.bigNodeWidth = evenFloor (
        (width
         - (2 * nodeMinSpacing)
        ) / 3
    );

    this.width =
        maxNodesOnLine * this.smallestNodeWidth
        + (maxNodesOnLine - 1) * nodeMinSpacing;
    this.height = height;
    this.xFactor = this.width;
    this.yFactor = this.height;

    this.tree = d3.layout.tree()
        .children(function(d) {
            if (d.solved) { return []; }
            return d.visibleChildren;
        })
        .separation(function(n1, n2) { return 1; })
    ;

    this.div = anchor
        .insert("div", ":first-child")
        .attr("id", "pt-" + this.svgId)
        .on("click", function() {
            // TODO: suspend the activeProofTree
            makeActive(self);
        })
    ;

    this.svg = this.div
        .insert("svg", ":first-child")
        .attr("id", "svg-" + this.svgId)
        .attr("width", this.width)
        .attr("height", this.height)
    ;

    this.proofDiv =
        anchor
        .append("div")
        .attr("id", "proof-" + this.svgId)
        .style("font-family", "monospace")
        .style("margin", "10px")
    ;

    this.error =
        anchor
        .append("div")
        .attr("id", "error-" + this.svgId)
        .style("font-family", "monospace")
        .style("margin", "10px")
        .style("background-color", "red")
        .style("display", "none")
    ;

    this.canvas =
        this.svg
        .append("g")
        //.attr("id", "viewport") // for SVGPan
        .attr("class", "canvas")
    // an okay approximation of the canvas initial translation
        .attr("transform",
              "translate("
              + this.width / maxNodesOnLine
              + ", "
              + 0
              + ")"
             )
    ;

    this.context =
        this.svg
        .append("g")
        .attr("class", "context")
    ;

    var contextDivWidth = this.bigNodeWidth - rectMargin.left - rectMargin.right;
    var contextHeight;

    this.context
        .append("foreignObject")
        .attr('x', rectMargin.left)
        .attr("width", contextDivWidth)
        .append("xhtml:body")
        .style("background-color", "rgba(0, 0, 0, 0)")
        .html('<div><p>Empty context</p></div>')
    // now retrieve the computed height of the div
        .attr("height", function() {
            contextHeight = this.firstChild.getBoundingClientRect().height;
            return contextHeight;
        })
    ;

    this.context
        .insert("rect", ":first-child")
        .attr("width", this.bigNodeWidth)
        .attr("height", contextHeight)
    ;

    this.debug =
        this.svg
        .append("g")
        .attr("class", "debug")
    ;

    var debugDivWidth = this.bigNodeWidth - rectMargin.left - rectMargin.right;
    var debugHeight;

    this.debug
        .append("foreignObject")
        .attr('x', this.width - this.bigNodeWidth + rectMargin.left)
        .attr("width", debugDivWidth)
        .append("xhtml:body")
        .style("background-color", "rgba(0, 0, 0, 0)")
        .html('<div><p>No debug information</p></div>')
        .attr("height", function() {
            debugHeight = this.firstChild.getBoundingClientRect().height
            return debugHeight;
        })
    ;

    this.debug
        .insert("rect", ":first-child")
        .attr("x", this.width - this.bigNodeWidth)
        .attr("width", this.bigNodeWidth)
        .attr("height", debugHeight)
    ;

/*
    this.svg
        .insert("script", ":first-child")
        .attr("xlink:href", this.roosterDir + "SVGPan.js")
    ;
*/

}

PT.ProofTree = ProofTree;

PT.handleKeyboard = function() {
    d3.select("body")
        .on("click", function() {
            if($(":focus").size() > 0) {
                activeProofTree = undefined;
            }
        })
        .on("keydown", keydownDispatcher)
    ;
}

function parseSVGTransform(a) {
    var b = {};
    for (var i in a = a.match(/(\w+\((\-?\d+\.?\d*,?)+\))+/g)) {
        var c = a[i].match(/[\w\.\-]+/g);
        b[c.shift()] = c;
    }
    return b;
}

function evenFloor(x) {
    var r = Math.floor(x);
    return (r % 2 === 0) ? r : r - 1;
}

ProofTree.prototype.nodeWidth = function(d) {
    return (this.isCurNode(d) || this.isCurNodeParent(d))
        ? this.bigNodeWidth
        : this.smallestNodeWidth
    ;
}

function treeDepth(root) {
    return (root.visibleChildren.length > 0)
        ? 1 + _(root.visibleChildren).map(treeDepth).max()
        : 0
    ;
}

ProofTree.prototype.newTheorem = function(
    theorem,
    tactics,           // set of tactics allowed (TODO: make this more dynamic)
    preAnimCallback,   // to be called once the data is ready
    postAnimCallback)  // to be called once the svg is ready
{

    var self = this;

    this.theorem = theorem;
    this.tactics = tactics;

    // hide previous proof result if any, show svg if hidden
    this.proofDiv.style("display", "none");
    this.svg.style("display", "");

    // reinitialize the viewport to a satisfying location
    this.canvas
        .attr("class", "canvas")
        .attr("transform",
              "translate("
              + this.width / maxNodesOnLine
              + ", "
              + 0
              + ")"
             )
    ;

    var success = false;

    this.syncQuery(theorem, function(response) {
        success = self.hInit(response, preAnimCallback, postAnimCallback);
    });

    return success;

}

function mkGoalNode(g, ndx) {
    return {
        "id": _.uniqueId(),
        "name": g.gGoal,
        "hyps": g.gHyps,
        "ndx": ndx + 1,
        "gid": g.gId,
        "offset": 0,
        "solved": false,
    };
}

function mkTacticNode(tactic, goals) {

    var children = _(goals)
        .map(mkGoalNode)
        .value()
    ;

    return {
        "id": _.uniqueId(),
        "name": tactic,
        "allChildren": children,
        "visibleChildren": children.slice(0, nbChildrenToShow),
        "offset": 0,
        "terminating": _(children).isEmpty(),
        "solved": false,
    };

}

ProofTree.prototype.tryAllTactics = function() {

    var self = this;

    var res = [];
    var unfocusedBefore;

    this.syncQueryUndo('idtac.', function(response) {
        unfocusedBefore = response.rGoals.unfocused;
        res.push(mkTacticNode('idtac.', response.rGoals.focused));
    });

    var run = function(t) {
        self.syncQueryUndo(t + '.', function(response) {
            if(isGood(response)) {
                if (_.isEqual(response.rGoals.unfocused, unfocusedBefore)) {
                    res.push(mkTacticNode(t + '.', response.rGoals.focused));
                } else {
                    res.push(mkTacticNode(t + '.', []));
                }
            }
/*
            else {
                console.log(
                    'Bad response for tactic ' + t + ': ',
                    response.rResponse.contents,
                    response
                );
            }
*/
        });
    }

    var curHyps = [];
    var curGoal = (isGoal(this.curNode)) ? this.curNode : this.curNode.parent;
    curHyps = curGoal.hyps;

    _(this.tactics).each(function(t) {

        switch (t) {
        case "destruct":
            _(curHyps).each(function(h) {
                run('destruct ' + h.hName);
            });
            break;
        case "induction":
            _(curHyps).each(function(h) {
                run('induction ' + h.hName);
            });
            break;
        case "intro":
            run('intro');
            run('intros');
            break;
        case "rewrite":
            _(curHyps).each(function(h) {
                run('rewrite -> ' + h.hName);
                run('rewrite <- ' + h.hName);
            });
            break;
        default:
            run(t);
            break;
        }
    });

    res =
        _(res)
        .uniq(false, function(e) {
            return JSON.stringify(
                _(e.allChildren)
                    .map(function(c) {
                        return {"name": c.name, "hyps": c.hyps};
                    })
                .value()
            );
        })
        .rest() // remove idtac
        .sortBy(function(e) { return e.allChildren.length; })
        .value()
    ;

    return res;

}

ProofTree.prototype.hInit = function(response, preAnimCallback, postAnimCallback) {

    var self = this;

    if (isBad(response)) {
        console.log(response.rResponse.contents);
        this.error.text(response.rResponse.contents);
        this.svg.style("display", "none");
        this.proofDiv.style("display", "none");
        this.error.style("display", "");
        return false;
    }
    this.error.style("display", "none");

    // There should only be one goal at that point
    this.rootNode = {
        "id": _.uniqueId(),
        "name": response.rGoals.focused[0].gGoal,
        "x0": 0.5,
        "y0": 0,
        "allChildren": [], // will be filled once this.curNode is set
        "ndx": 1,
        "depth": 0, // need to set depth for isGoal() to work early
        "offset": 0,
        "hyps": [],
        "visibleChildren": [],
    };

    this.curNode = this.rootNode;

    this.rootNode.allChildren = this.tryAllTactics();

    this.update(this.rootNode);

    preAnimCallback(self);

    window.setTimeout(function() { postAnimCallback(self); }, animationDuration);

    return true;

}

function hasParent(n) {
    return n.hasOwnProperty('parent');
}

function hasGrandParent(n) {
    return n.hasOwnProperty('parent')
        && n.parent.hasOwnProperty('parent');
}

ProofTree.prototype.isRootNode = function(n) { return n.id === this.rootNode.id; }

ProofTree.prototype.isCurNode = function(n) { return n.id === this.curNode.id; }

ProofTree.prototype.isCurNodeParent = function(n) {
    return hasParent(this.curNode) && this.curNode.parent.id === n.id;
}

ProofTree.prototype.isCurNodeChild = function(n) {
    if (hasParent(n) && this.isCurNode(n.parent)) { return true; }
    return false;
}

ProofTree.prototype.isCurNodeGrandChild = function(n) {
    if (hasParent(n) && this.isCurNodeChild(n.parent)) { return true; }
    return false;
}

ProofTree.prototype.isCurNodeSibling = function(n) {
    return !this.isCurNode(n) && hasParent(n) && this.isCurNodeParent(n.parent);
}

ProofTree.prototype.update = function(source) {

    var self = this;
    var curNode = this.curNode; // expected to stay constant throughout

    // if the viewpoint has been zoomed, cancel the zoom so that the computed
    // sizes are correct
    var m = parseSVGTransform(this.canvas.attr('transform'));
    if (m.hasOwnProperty('matrix')) {
        m = m.matrix;
        this.canvas.attr('transform',
                    'matrix(1'
                    + ',' + m[1]
                    + ',' + m[2]
                    + ', 1'
                    + ',' + m[4]
                    + ',' + m[5]
                    +')')
        ;
    }

    var nodes = this.tree.nodes(this.rootNode);

    var links = this.tree.links(nodes);

    var node =
        this.canvas
        .selectAll("g.node")
        .data(nodes, function(d) {
            return d.id || (d.id = _.uniqueId());
        })
    ;

    var link =
        this.canvas
        .selectAll("path")
        .data(links, function(d) {
            return d.id = d.source.id + "," + d.target.id;
        });

    var nodeEnter = node.enter();

    var gs = nodeEnter
        .append("g")
        .attr("class", "node")
        .on("click", this.click.bind(this))
    ;

    var fo =
        gs
        .append("foreignObject")
        .attr("width", function(d) {
            return self.nodeWidth(d) - rectMargin.left - rectMargin.right;
        })
    ;

    fo
        .append("xhtml:body")
        .style("background-color", "rgba(0, 0, 0, 0)")
        .each(function(d) {

            var jqObject = $(d3.select(this).node());
            var jQDiv = $("<div>").addClass("node");
            jqObject.append(jQDiv);

            if (isGoal(d)) {

                if (hasGrandParent(d)) {

                    // clone since I'm going to pull() from it
                    var gpHyps = _(_(d.parent.parent.hyps).clone());

                    var removed = [], changed = [], added = [];

                    _(d.hyps).each(function(h) {

                        var previousH =
                            _(gpHyps).find(function(h0) {
                                return h0.hName === h.hName;
                            });

                        if (previousH === undefined) {
                            added.push(h);
                        } else {
                            if (JSON.stringify(previousH) !== JSON.stringify(h)) {
                                changed.push({"before": previousH, "after": h});
                            }
                            gpHyps.pull(previousH);
                        }

                    });

                    removed = gpHyps.value();

                    _(removed).each(function(h) {
                        jQDiv.append(
                            $("<span>")
                                .addClass("removed")
                                .html('⊖ ' + showHypothesis(h))
                        );
                        jQDiv.append($("<br>"));
                    });

                    var fo = d3.select(this);

                    _(changed).each(function(hs) {

                        fo
                            .select("div")
                            .append("span")
                            .html("&nbsp;&nbsp;" + showHypothesis(hs.after))
                            .attr("class", "changed")
                            .on("mouseover", function() {
                                d3.select(this)
                                    .attr("class", "removed")
                                    .html("&nbsp;&nbsp;" + showHypothesis(hs.before))
                                ;
                            })
                            .on("mouseout", function(d) {
                                d3.select(this)
                                    .attr("class", "changed")
                                    .html("&nbsp;&nbsp;" + showHypothesis(hs.after))
                                ;
                            })
                        ;

                        fo.select("div").append("br");

                    });

                    _(added).each(function(h) {
                        jQDiv.append(
                            $("<span>")
                                .addClass("added")
                                .html('⊕ ' + showHypothesis(h))
                        );
                        jQDiv.append($("<br>"));
                    });

                    jQDiv.append($('<hr>'));

                } else {

                    _(d.hyps).each(function(h) {
                        jQDiv.append(
                            $("<span>")
                                .addClass("added")
                                .html('⊕ ' + showHypothesis(h))
                        );
                    });

                    if (!_(d.hyps).isEmpty()) { jQDiv.append($('<hr>')); }

                }


                jQDiv.append($("<span>").html(showTerm(d.name)));

            } else { // not a goal, but a tactic

                jQDiv
                    .css("text-align", "center")
                    .append(
                        $("<span>").text(d.name)
                    )
                ;

            }

        })
    ;

    fo
        .attr("height", function(d) {
            var h = this.firstChild.getBoundingClientRect().height;
            d.height = h + 2 * nodeStroke;
            return h;
        })
        .attr("transform", function(d) {
            return 'translate(-'
                + ((self.nodeWidth(d) / 2) - rectMargin.left)
                + ', -'
                + ((d.height / 2) - rectMargin.top)
                + ')'
            ;
        })
    ;

    // Compute the new visible nodes, determine the translation and zoom

    var visibleNodes = [];
    if (hasParent(curNode)) {
        visibleNodes = visibleNodes.concat(curNode.parent);
    }
    visibleNodes = visibleNodes.concat([curNode]);
    visibleNodes = visibleNodes.concat(curNode.visibleChildren || []);

    visibleNodes = visibleNodes.concat(
        _(curNode.visibleChildren || [])
        .map(function(n) { return (n.visibleChildren || []); })
        .flatten()
        .value()
    );

    var minX = _(visibleNodes)
        .map(function(d) { return d.x; })
        .min()
        .value();

    var maxX = _(visibleNodes)
        .map(function(d) { return d.x; })
        .max()
        .value();

    var minY = _(visibleNodes)
        .map(function(d) { return d.y; })
        .min()
        .value();

    var maxY = _(visibleNodes)
        .map(function(d) { return d.y; })
        .max()
        .value();

    // We want the current node to stay fixed as we scroll through
    // its children, so we always center the viewpoint around it

    var leftdX = curNode.x - minX;
    var rightdX = maxX - curNode.x;
    var halfdX = Math.max(leftdX, rightdX);
    var minX = curNode.x - halfdX;
    var maxX = curNode.x + halfdX;
    var dX = maxX - minX;
    var dY = maxY - minY;
    var allChildren = _(curNode.allChildren);

    var allGrandChildren = _(allChildren).map(function(c) {
        if (c.hasOwnProperty('allChildren')) {
            return _(c.allChildren).value();
        }
        return [];
    }).flatten();

    var firstChild = allChildren.first();
    var lastChild = allChildren.last();
    var firstGrandChild = allGrandChildren.first();
    var lastGrandChild = allGrandChildren.last();

    var visibleChildren = _(curNode.visibleChildren);
    var visibleGrandChildren = _(visibleChildren).map(function(c) {
        if (c.hasOwnProperty('visibleChildren')) {
            return _(c.visibleChildren).value();
        }
        return [];
    }).flatten();
    var firstVisibleChild = visibleChildren.first();
    var lastVisibleChild = visibleChildren.last();

    var leftmostNode = firstGrandChild;
    if (leftmostNode === undefined) { leftmostNode = firstChild; }
    if (leftmostNode === undefined) { leftmostNode = curNode; }

    var rightmostNode = lastGrandChild;
    if (rightmostNode === undefined) { rightmostNode = lastChild; }
    if (rightmostNode === undefined) { rightmostNode = curNode; }

    // We need to scale the view so that two adjacent nodes do not overlap and
    // are well spaced.

    // siblings = [ [gc0, gc1], [gc1, gc2], ... ] ++ [ [c0, c1], [c1, c2], ... ]
    var gcSiblings =
        isGoal(curNode)
        ? _.zip(visibleGrandChildren.value(), visibleGrandChildren.rest().value())
        : [] // because grand-children don't appear for tactic nodes
    ;
    gcSiblings.pop(); // removes [gc_last, undefined] at the end
    var cSiblings = _.zip(visibleChildren.value(), visibleChildren.rest().value());
    cSiblings.pop(); // removes [c_last, undefined] at the end
    var siblings = gcSiblings.concat(cSiblings);

    var siblingsDistances = siblings.map(function(e) {
        return (e[1].x - e[0].x);
    });

    var siblingMinDistance = _.min(siblingsDistances);

    this.xFactor = (siblingMinDistance === Infinity)
        ? this.xFactor
        : ((this.smallestNodeWidth + nodeMinSpacing)
           / siblingMinDistance)
    ;

    // the top-most node is always the parent if it exists, the current otherwise
    var topmostNode = hasParent(curNode) ? curNode.parent : curNode;

    // the bottom-most node is either the grand-child of largest height...
    var bottommostNode =
        (isGoal(curNode))
        ? allGrandChildren.max(function(c) { return c.height; }).value()
        : -Infinity
    ;
    // ...or the child of largest height...
    if (bottommostNode === -Infinity) {
        bottommostNode = allChildren.max(function(c) { return c.height; }).value();
    }
    // ...or the current node
    if (bottommostNode === -Infinity) { bottommostNode = curNode; }

    this.yFactor = (dY === 0)
        ? this.yFactor
        : ((this.height - (topmostNode.height / 2) - (bottommostNode.height / 2)) / dY)
    ;

    gs
        .attr("transform", function(d) {
            if (hasParent(d)) {
                // non-roots are spawned at their parent's (cX0, cY0)
                d.cX0 = d.parent.cX0;
                d.cY0 = d.parent.cY0;
            } else {
                // the root stores its own (x0, y0)
                d.cX0 = d.x0 * self.xFactor;
                d.cY0 = d.y0 * self.yFactor;
            }
            return "translate(" + d.cX0 + "," + d.cY0 + ")";
        })

    gs
        .insert("rect", ":first-child")
        .attr("x", function(d) {
            return this.nextSibling.getBBox().x - self.nodeWidth(d) / 2;
        })
        .attr("y", function(d) {
            return this.nextSibling.getBBox().y - d.height / 2;
        })
        .attr("width", function(n) {
            var w = rectMargin.left
                + this.nextSibling.getBBox().width
                + rectMargin.right
            ;
            return w - nodeStroke;
        })
        .attr("height", function(n) {
            var h = rectMargin.top
                + this.nextSibling.getBBox().height
                + rectMargin.bottom;
            return h - nodeStroke;
        })
        .attr("stroke-width", nodeStroke)
    ;

    gs
        .append("text")
        .attr('class', 'leftarrow')
        .text('←')
        .attr("x", function() {
            var pb = this.parentElement.firstChild.getBBox();
            return pb.x;
        })
        .attr("y", function() {
            var pb = this.parentElement.firstChild.getBBox();
            return pb.y + pb.height + 26;
        })
        .on('click', function(n) {
            self.shiftLeft(n);
            d3.event.stopPropagation();
        })
    ;

    gs
        .append("text")
        .attr('class', 'rightarrow')
        .text('→')
        .attr("x", function() {
            var pb = this.parentElement.firstChild.getBBox();
            return pb.x + pb.width - 26;
        })
        .attr("y", function() {
            var pb = this.parentElement.firstChild.getBBox();
            return pb.y + pb.height + 26;
        })
        .on('click', function(n) {
            self.shiftRight(n);
            d3.event.stopPropagation();
        })
    ;

    node
        .selectAll('text.leftarrow')
        .classed('invisible', function(d) {
            return !(
                // visible when:
                !d.solved
                    && d.offset > 0
                    && (self.isCurNode(d) || self.isCurNodeChild(d))
                    && !_.isEmpty(d.visibleChildren)
            );
        })
    ;

    node
        .selectAll('text.rightarrow')
        .classed('invisible', function(d) {
            return !(
                // visible when:
                ! d.solved
                    && d.offset + nbChildrenToShow < _(d.allChildren).size()
                    && (self.isCurNode(d) || self.isCurNodeChild(d))
                    && !_.isEmpty(d.visibleChildren)
            );
        })
    ;

    // We want
    // (firstVisibleChild.cX + lastVisibleChild.cX) / 2 = curNode.cX
    // We offset all the descendants to achieve this
    var xMiddle =
        (firstVisibleChild !== undefined && lastVisibleChild !== undefined)
        ? (firstVisibleChild.x + lastVisibleChild.x) / 2
        : curNode.x
    ;

    var descendantsXOffset = curNode.x - xMiddle;

    _(nodes)
        .each(function(n) {
            if (self.isCurNodeChild(n) || self.isCurNodeGrandChild(n)) {
                n.cX = (n.x + descendantsXOffset) * self.xFactor;
            } else if (self.isCurNodeSibling(n)) {
                var smallBigDelta = self.bigNodeWidth - self.smallestNodeWidth;
                if (n.ndx < curNode.ndx) {
                    n.cX = n.x * self.xFactor - smallBigDelta / 2;
                } else {
                    n.cX = n.x * self.xFactor + smallBigDelta / 2;
                }
            } else if (self.isCurNodeParent(n)) {
                n.cX = curNode.x * self.xFactor;
            } else {
                n.cX = n.x * self.xFactor;
            }
            n.cY = n.y * self.yFactor;
        })
    ;

    this.canvas
        .transition()
        .duration(animationDuration)
        .attr("transform",
              "translate("
              + (
                  this.width / 2 - curNode.cX
/*
                  (dX === 0)
                      ? (width / 2 - minX * xFactor)
                      : (smallestNodeWidth / 2 - minX * xFactor)
*/
              )
              + ", "
              + (
                  (dY === 0)
                      ? topmostNode.height / 2
                      : (topmostNode.height / 2 - minY * self.yFactor)
                )
              + ")")
    ;

    node
        .transition()
        .duration(animationDuration)
        .attr("transform", function(d) {
            return "translate(" + d.cX + ", " + d.cY + ")";
        })
    ;

    node
        .selectAll('rect')
        .transition()
        .duration(animationDuration)
        .attr("width", this.nodeWidth.bind(this))
        .attr("x", function(d) {
            return this.nextSibling.getBBox().x - self.nodeWidth(d) / 2;
        })
    ;

    node
    // Webkit bug, cannot selectAll on camel case names :(
        .selectAll(function() {
            return this.getElementsByTagName("foreignObject");
        })
        .transition()
        .duration(animationDuration)
        .attr("width", function(d) {
            return self.nodeWidth(d) - rectMargin.left - rectMargin.right;
        })
        .attr("transform", function(d) {
            return 'translate(-'
                + ((self.nodeWidth(d) / 2) - rectMargin.left)
                + ', -'
                + ((d.height / 2) - rectMargin.top)
                + ')'
            ;
        })
    ;

    this.canvas
        .selectAll("rect")
        .classed("tactic", function(d) { return isTactic(d) && !d.solved; })
        .classed("goal", function(d) { return isGoal(d) && !d.solved; })
        .classed("solved", function(d) { return (d.solved); })
        .classed("current", this.isCurNode.bind(this))
    ;

    var nodeExit = node.exit();

    var nodeIsExiting = function(n1) {
        var exiting = false;
        // Apparently 'some' is not properly overridden for selections,
        // so use 'each' instead...
        nodeExit.each(function(n2) {
            if (n1.id === n2.id) { exiting = true; }
        });
        return exiting;
    }

    nodeExit
        .transition()
        .duration(animationDuration)
        .attr("transform", function(d) {
            // if the previous root node tries to exit, just leave it where it was
            if (!hasParent(d)) {
                return "translate(" + d.cX + "," + d.cY + ")";
            }
            var parentAlsoExiting = nodeIsExiting(d.parent);
            var nodeToReach = (parentAlsoExiting && hasGrandParent(d))
                ? d.parent.parent
                : d.parent
            ;
            return "translate(" + nodeToReach.cX + "," + nodeToReach.cY + ")";
        })
        .style("opacity", "0")
        .remove()
    ;

    link
        .enter()
        .insert("path", "g")
        .attr("class", "link")
        .attr("id", function(d) { return d.id; })
        .attr("d", function(d) {
            var o = {"x": d.source.cX0, "y": d.source.cY0};
            return diagonal({"source": o, "target": o});
        })
    ;

    link
        .transition()
        .duration(animationDuration)
        .attr("d", function(d) {
            return diagonal(
                {
                    "source": {"x": d.source.cX, "y": d.source.cY,},
                    "target": {"x": d.target.cX, "y": d.target.cY,},
                }
            );
        })
    ;

    link
        .exit()
        .transition()
        .duration(animationDuration)
        .attr("d", function(d) {
            var sourceAlsoExiting = nodeIsExiting(d.source);
            var sourceNode = (sourceAlsoExiting && hasParent(d.source))
                ? d.source.parent
                : d.source
            ;
            var o = {"x": sourceNode.cX, "y": sourceNode.cY};
            return diagonal({"source": o, "target": o});
        })
        .style("opacity", "0")
        .remove()
    ;

    /*
      It is important to update cX0 for all nodes so that we can uniformly
      initialize links to start between their source's cX0 and their target's
      cX0.
      Without this, links created from nodes that have moved away from their
      cX0 will seem to appear from the node's old position rather than its
      current one.
    */
    _(nodes).each(function(d) {
        d.x0 = d.x;
        d.y0 = d.y;
        d.cX0 = d.cX;
        d.cY0 = d.cY;
    });

    this.updateContext();

    this.animationRunning = true;
    window.setTimeout(function() { self.animationRunning = false; }, animationDuration);

}

ProofTree.prototype.updateVisibleChildren = function(n) {
    n.visibleChildren = n.allChildren.slice(n.offset, n.offset + nbChildrenToShow);
    this.update(n);
}

ProofTree.prototype.shiftLeft = function(n) {
    if (n.solved) { return; }
    if (n.offset > 0) {
        n.offset--;
        this.updateVisibleChildren(n);
    }
}

ProofTree.prototype.shiftRight = function(n) {
    if (n.solved) { return; }
    if (n.offset + nbChildrenToShow < n.allChildren.length) {
        n.offset++;
        this.updateVisibleChildren(n);
    }
}

ProofTree.prototype.click = function(d) {

    if (this.animationRunning) { return; }

    if (d.solved) {
        if (hasParent(d)) {
            this.click(d.parent);
        }
        return;
    }

    // when the user clicks on a tactic node below
    // bring them to the first unsolved goal instead
    if(isTactic(d) && d.depth > this.curNode.depth && d.allChildren.length > 0) {
        var firstUnsolved = _(d.allChildren)
            .find(function(e) { return !e.solved; });
        if (firstUnsolved !== undefined) {
            this.click(firstUnsolved);
            return;
        }
    }

    this.navigateTo(d);

    if (!d.hasOwnProperty('allChildren') || d.allChildren.length === 0) {
        if (isGoal(d)) {
            d.allChildren = this.tryAllTactics();
        }
        // otherwise, this is a terminating tactic for this goal!
        else {
            this.solved(d);
        }
    }

    this.expand(d);
    this.update(d);

}

// called when n has been solved
ProofTree.prototype.solved = function(n) {

    var self = this;

    n.solved = true;
    n.visibleChildren = [];
    //n.allChildren = [];
    collapse(n);
    if (hasParent(n)) {
        this.navigateTo(n.parent);
        this.animationRunning = true;
        window.setTimeout(function () {
            self.childSolved(n.parent);
            self.update(n.parent);
            self.animationRunning = false;
        }, animationDuration);
    } else {
        window.setTimeout(function () {
            self.qedCallback(self);
        }, animationDuration);
    }
}

// called when a child of n has become solved
ProofTree.prototype.childSolved = function(n) {
    if (isGoal(n)) {
        this.solved(n);
    } else {
        // Bubble up if this was the last subgoal
        var lastSubgoal =
            _(n.allChildren)
            .every(function(n) { return n.solved === true; })
        ;
        if (lastSubgoal) { this.solved(n); }
    }
}

function toggle(d) {
    if (d.visibleChildren) {
        d.visibleChildren = [];
    } else {
        d.visibleChildren = d.allChildren;
    }
}

function collapse(d) {
    if (d.visibleChildren) {
        d.visibleChildren = [];
    }
}

function collapseChildren(d) {
    _(d.visibleChildren)
        .forEach(function(n) {
            collapse(n);
        })
    ;
}

function collapseExcept(d, e) {
    if (d.visibleChildren) {
        d.visibleChildren = [e];
    }
}

ProofTree.prototype.expand = function(d) {
    d.visibleChildren = d.allChildren.slice(d.offset, d.offset + nbChildrenToShow);
    if (isGoal(d)) {
        _(d.visibleChildren)
            .each(function(c) {
                c.visibleChildren =
                    c.allChildren.slice(c.offset,
                                        c.offset + nbChildrenToShow);
            });
    }
}

ProofTree.prototype.commonAncestor = function(n1, n2) {
    if (n1.id === this.rootNode.id || n2.id === this.rootNode.id) { return this.rootNode; }
    if (n1.id === n2.id) { return n1; }
    if (n1.depth < n2.depth) {
        return this.commonAncestor(n1, n2.parent);
    } else if (n1.depth > n2.depth) {
        return this.commonAncestor(n1.parent, n2);
    } else {
        return this.commonAncestor(n1.parent, n2.parent);
    }
}

/*
  Returns an array [n1, a, b, ..., z, n2] such that n1 -> a -> b -> ... -> z -> n2
  is the shortest path from a to b in the tree
*/
function path(n1, n2) {
    if (n1.id === n2.id) { return [n1]; }
    if (n1.depth < n2.depth) {
        var res = path(n1, n2.parent);
        res.push(n2);
        return res;
    } else if (n1.depth > n2.depth) {
        var res = path(n1.parent, n2);
        res.unshift(n1);
        return res;
    } else {
        var res = path(n1.parent, n2.parent);
        res.unshift(n1);
        res.push(n2);
        return res;
    }
}

function hasVisibleChild(n) {
    return (n.visibleChildren && n.visibleChildren[0]) ? true : false;
}

/*
We need to compute how many layers of focusing are solved by a terminating
tactic because of the way Undo works.
Since we Undo every proved branch before navigating to another branch, this
depth is always how deep the node is to its first ancestor with more than
one child (since the other child will then remain to be proved).
*/
function depthSolved(tacNode) {

    if (!hasGrandParent(tacNode)) { return 1; }

    if (_(tacNode.children).size() <= 1) {
        return 1 + depthSolved(tacNode.parent.parent);
    } else {
        return 0;
    }

}

ProofTree.prototype.navigateTo = function(dest) {

    var self = this;

    var a = this.commonAncestor(this.curNode, dest);

    var p = path(this.curNode, dest);

    // morally, q = [ [p0, p1], [p1, p2], ... ]
    var q = _.zip(p, _(p).rest().value());
    q.pop(); // remove the extra [p_last, undefined] at the end

    _(q)
        .each(function(elt) {
            var src = elt[0];
            var dst = elt[1];

            var goingUp = src.depth > dst.depth;

            if (goingUp) {

                collapseChildren(src);
                if (isGoal(src)) { collapse(src); }

                if (isTactic(src)) {
                    // need to Undo as many times as the focus depth difference
                    // between before and after the terminating tactic + 1
                    if(src.terminating) {
                        _(_.range(depthSolved(src))).each(function() {
                            self.syncQuery('Undo.', hIgnore);
                        });
                    }
                    self.syncQuery('Undo.', hIgnore);
                } else {
                    // 'Back.' does not work in -ideslave
                    // 'Back.' takes one step to undo 'Show.'
                    // 'Undo.' works in -ideslave
                    // 'Undo.' does not care about 'Show.' commands

                    // Undo the 'Focus.' command.
                    // Do not use 'Unfocus.' as it is itself undone by 'Undo.'
                    self.syncQuery('Undo.', hIgnore);
                }
            } else { // going down

                // hide sibling tactic nodes
                if (isGoal(src)) {
                    collapseExcept(src, dst);
                }

                if (isTactic(dst)) {
                    self.syncQuery(dst.name, hIgnore);
                } else {
                    self.syncQuery('Focus ' + dst.ndx + '.', hIgnore);
                }

            }
        })
    ;

    this.curNode = dest;

}

function isTactic(n) { return (n.depth % 2 === 1); }

function isGoal(n) { return (n.depth % 2 === 0); }

ProofTree.prototype.syncRequest = function(r, q, h) {
    var self = this;
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: this.roosterDir + r,
        data: {query : q},
        async: false,
        success: function(response) {
            //console.log("response", response);
            if (r === "query") { self.updateDebug(response); }
            h(response);
        }
    });
}

ProofTree.prototype.syncQuery = function(q, h) { this.syncRequest('query', q, h); }
ProofTree.prototype.syncQueryUndo = function(q, h) { this.syncRequest('queryundo', q, h); }

function hIgnore(response) { }

function updateNodeHeight(selector) {
    var div = selector.select('div');

    selector
    // Webkit bug, cannot selectAll on camel case names :(
        .selectAll(function() {
            return this.getElementsByTagName("foreignObject");
        })
        .attr("height", function() {
            var height = div[0][0].getBoundingClientRect().height;
            selector
                .select('rect')
                .attr('height', height)
            ;
            return height;
        })
    ;
}

// TODO: this should use d3 data binding rather than manual management...
ProofTree.prototype.updateContext = function() {

    var contextDiv = $(this.context.select('div')[0]);
    var curGoal = (isGoal(this.curNode)) ? this.curNode : this.curNode.parent;
    var hypsLookup = {};
    _(curGoal.hyps)
        .each(function(h) {
            hypsLookup[h.hName] = showTermInline(h.hType);
        })
    ;

    contextDiv.html("");

    // matches identifiers in the first group, and the rest in the second group
    var grouper = /([a-zA-Z\d_]+)|([^a-zA-Z\d_]+)/g;

    /*
      adding to the context only those variables that are not referred to in the
      type of others. those referred to will have their type in tooltips
      wherever they are mentioned.
      we collect such references by processing the hypotheses from the back.
     */
    var seen = [];
    _(curGoal.hyps).forEachRight(function(h) {
        if (!_(seen).contains(h.hName)) {
            var p = $("<p>");
            p.append($("<span>").text(h.hName + " : "));
            var group;
            var type = showTermInline(h.hType);
            while ((group = grouper.exec(type)) !== null) {
                if (group[1] !== undefined) { // matched an identifier
                    var id = group[0];
                    seen.push(id);
                    if (hypsLookup[id] !== undefined) {
                        p.append(
                            $("<span>")
                                .text(id)
                                .attr("title", hypsLookup[id])
                                .css("font-weight", "bold")
                                .css("color", "green")
                        );
                    } else {
                        p.append($("<span>").text(id));
                    }
                } else if (group[2] !== undefined) { // matched something else
                    p.append($("<span>").text(group[0]));
                }
            }
            contextDiv.prepend(p);
        }
    });

    if (contextDiv.html() === "") {
        contextDiv.append("p").text("Empty context");
    }

    updateNodeHeight(this.context);

}

ProofTree.prototype.updateDebug = function(response) {

    var debugDiv = this.debug.select('div');
    if (response.rGoals.focused.length > 0) {
        debugDiv.html(response.rGoals.focused[0].gGoal);
    } else {
        debugDiv.html(response.rResponse.contents[0]);
    }

    updateNodeHeight(this.debug);

}

function keydownDispatcher() {
    if (activeProofTree !== undefined) {
        activeProofTree.keydownHandler.call(activeProofTree);
    }
}

ProofTree.prototype.keydownHandler = function() {

    var curNode = this.curNode;

    if (this.animationRunning) {
        // all keys are frozen during animation
        d3.event.preventDefault();
        return;
    }

    switch (d3.event.keyCode) {

    case 37: case 65: // Left, a
        this.shiftLeft(curNode);
        break;

    case 39: case 68: // Right, d
        this.shiftRight(curNode);
        break;

    case 38: case 87: // Up, w
        if(hasParent(curNode)) {
            this.click(curNode.parent);
        }
        break;

    case 40: case 83: // Down, s
        if (isTactic(curNode)) {
            var dest = _(curNode.visibleChildren).find(function(n) {
                return !(n.solved);
            });
            if (dest) { this.click(dest); }
        } else {
            if (curNode.visibleChildren[0]) {
                this.click(curNode.visibleChildren[0]);
            }
        }
        break;

    case 49: case 97: // 1, K1
        if (curNode.visibleChildren.length > 0) {
            this.click(curNode.visibleChildren[0]);
        }
        break;

    case 50: case 98: // 2, K2
        if (curNode.visibleChildren.length > 1) {
            this.click(curNode.visibleChildren[1]);
        }
        break;

    case 51: case 99: // 3, K3
        if (curNode.visibleChildren.length > 2) {
            this.click(curNode.visibleChildren[2]);
        }
        break;

    default: return;
    }

    // if we haven't returned, we don't want the normal key behavior
    d3.event.preventDefault();

}

function makeActive(prooftree) {
    activeProofTree = prooftree;
}

PT.proofFrom = function(t) {

    if (isGoal(t)) {
        return PT.proofFrom(_(t.allChildren).find("solved"));
    }

    if (isTactic(t)) {
        return [
            t.name,
            _(t.allChildren).map(PT.proofFrom).value(),
        ];
    }

    console.log("t is neither a goal nor a tactic", t);

}

function repeat(n, s) { return Array(n + 1).join(s); }

PT.pprint = function(proof, indentation) {
    if (_.isEmpty(proof)) { return ""; }
    var fst = proof[0];
    var snd = proof[1];
    var indent = repeat(2 * indentation, "&nbsp;");
    if (_.isEmpty(snd)) { return indent + "{ " + fst + " }<br>"; }
    return indent + "{ " + fst + "<br>"
        + _(snd).reduce(
            function(acc, elt) {
                return acc + PT.pprint(elt, indentation + 1)
            },
            ""
        )
        + indent + "}<br>"
    ;
}

function isBad(response) {
    return response.rResponse.tag === "Fail";
}

function isGood(response) {
    return response.rResponse.tag === "Good";
}

function contents(response) {
    return response.rResponse.contents;
}

ProofTree.prototype.replayThisProof = function(proof) {

    if (!_.isEmpty(proof)) {
        var fst = proof[0];
        var snd = proof[1];
        this.syncQuery(fst, function(response) {
            if (isGood(response)) {
                _(snd).each(replay);
            } else {
                console.log("Replay failed on applying " + fst);
                console.log("Error: " + contents(response));
            }
        });
    }

}

ProofTree.prototype.proof = function() {
    return PT.proofFrom(this.rootNode);
}

ProofTree.prototype.replay = function() {
    this.replayThisProof(PT.proofFrom(this.rootNode));
}

ProofTree.prototype.qed = function() {
    this.syncQuery("Qed.", function(response) {
        if (isBad(response)) {
            console.log("Qed failed, error:" + contents(response));
        }
    });
}

ProofTree.prototype.displayThisProof = function(proof) {
    this.svg.style("display", "none");
    this.proofDiv
        .style("display", "")
        .html(
            "Proof.<br>"
                + PT.pprint(proof, 1)
                + "Qed."
        )
    ;
}

ProofTree.prototype.displayProof = function() {
    this.displayThisProof(PT.proofFrom(this.rootNode));
}

function showBindersPar(t) {
    if (_.isEmpty(t)) { return ""; }
    return " (" + showBinder(t[0]) + ")" + showBindersPar(_(t).rest().value());
}

function showBinders(t) {
    if (_.isEmpty(t)) { return ""; }
    if (t.length === 1) { return showBinder(t[0]);  }
    return " (" + showBinder(t[0]) + ")" + showBindersPar(_(t).rest().value());
}

function showBinder(t) {
    return showNames(t[0]) + ": " + showTermAux(t[1], 0, 0, false);
}

function showNames(t) {
    if (_.isEmpty(t)) { return ""; }
    return t[0] + " " + showNames(_(t).rest().value());
}

function showTerm(t) {
    return showTermAux(t, 0, 0, true);
}

function getIndent(depth) {
    return repeat(2 * depth, "&nbsp;");
}

var precedence = 0;
var precMin    = precedence++;
var precForall = precedence++;
var precArrow  = precedence++;
var precEqual  = precedence++;
var precAnd    = precedence++; var precOr = precAnd;
var precPlus   = precedence++; var precMinus = precPlus;
var precMult   = precedence++;
var precApp    = precedence++;

function showTermAux(t, indentation, precParent, newline) {
    var c = t.contents;

    var indent = getIndent(indentation);

    var par = function(precOp, text) {
        if (precOp <= precParent) {
            return "(" + text + ")";
        } else {
            return text;
        }
    };

    var showOp = function(c, op, precOp) {
        return par(
            precOp,
            showTermAux(c[0].contents[1], 0, precOp, false)
                + " " + op + " "
                + showTermAux(c[1], 0, precOp, false)
        );
    };

    switch (t.tag) {

    case "Var":
        return c;

    case "Forall":
console.log("precForall", precForall, "precParent", precParent);
        return par(
            precForall,
            "∀ " + showBinders(c[0]) + ","
                + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
                + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Arrow":
        return showTermAux(c[0], indentation, precArrow, false)
            + " →" + (newline ? "<br/>" + indent : " ")
            + showTermAux(c[1], indentation, precParent, newline);

    case "App":

        // handling special case of infix operators I want to pretty print
        if (c[0].tag == "App") {
            switch (c[0].contents[0].contents) {

            case "eq":
                return showOp(c, "=", precEqual);

            case "plus":
                return showOp(c, "+", precPlus);

            case "minus":
                return showOp(c, "-", precMinus);

            case "mult":
                return showOp(c, "*", precMult);

            case "andb":
                return showOp(c, "&&", precAnd);

            case "orb":
                return showOp(c, "||", precOr);

            default:
                // nothing, fall through

            };
        }

        return par(
            precApp,
            showTermAux(c[0], 0, precApp, false) + " "
                + showTermAux(c[1], 0, precApp, false)
        );

    default:
        return "Unknown tag " + t.tag;

    };
}

function showHypothesis(h) {
    return h.hName + " : " + showTermAux(h.hType, 0, 0, false);
}

function showTermInline(t) {
    return showTermAux(t, 0, 0, false);
}
