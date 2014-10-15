
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
var nbDisplayedTactics = +Infinity;
var nbDisplayedGoals   = +Infinity; // per displayed tactic
var nbVisibleTactics = 1;
var nbVisibleGoals   = 2; // per focused tactic
var animationDuration = 420;
var tacticNodeRounding = 10;
var goalNodeRounding = 0;
var tacticNodeWidth = 250;
$(document).ready(function() {
    setupTextareaResizing();
});

// CHECKS
function assert(condition, message) {
    if (!condition) {
        alert(message);
        throw message || "Assertion failed";
    }
}
assert(nbDisplayedTactics >= nbVisibleTactics, "Make sure: nbDisplayedTactics >= nbVisibleTactics");
assert(nbDisplayedGoals >= nbVisibleGoals, "Make sure: nbDisplayedGoals >= nbVisibleGoals");

// COMPUTED GLOBALS
var activeProofTree = undefined;
var maxVisibleNodesOnLine = nbVisibleTactics * nbVisibleGoals;
var diagonal = d3.svg.diagonal();

// These tactic sets each build on top of the previous one
PT.tSet = [
    'simpl',
    'simpl in *',
    'reflexivity',
    'intro',
    'rewrite',
    'destruct',
    'induction',
    'inversion',
    'left',
    'right',
    'discriminate',
];
PT.tReflexivity  = PT.tSet.slice(0, 1 + PT.tSet.indexOf('reflexivity'));
PT.tIntro        = PT.tSet.slice(0, 1 + PT.tSet.indexOf('intro'));
PT.tRewrite      = PT.tSet.slice(0, 1 + PT.tSet.indexOf('rewrite'));
PT.tDestruct     = PT.tSet.slice(0, 1 + PT.tSet.indexOf('destruct'));
PT.tInduction    = PT.tSet.slice(0, 1 + PT.tSet.indexOf('induction'));
PT.tInversion    = PT.tSet.slice(0, 1 + PT.tSet.indexOf('inversion'));
PT.tDiscriminate = PT.tSet.slice(0, 1 + PT.tSet.indexOf('discriminate'));
// These ones are more specific
PT.tCompute = PT.tReflexivity.concat(['compute']);

// [width] and [height] are the wanted ones, it might end up slightly smaller
function ProofTree(anchor, width, height, qed, roosterDir, onError) {

    var self = this;

    this.anchor = anchor;
    this.qedCallback = qed;
    this.onError = onError;
    this.roosterDir = (typeof roosterDir === "undefined") ? "./" : roosterDir + "/";

    this.svgId = _.uniqueId();

    this.animationRunning = false;

    this.bottomNodeWidth = evenFloor(
        (width
         - ((maxVisibleNodesOnLine - 1) * nodeMinSpacing)
        ) / maxVisibleNodesOnLine
    );

    this.rootNodeWidth = width / 2;

    this.width = width;
        /*
        maxVisibleNodesOnLine * this.bottomNodeWidth
        + (maxVisibleNodesOnLine - 1) * nodeMinSpacing;
        */
    this.height = height;
    this.xFactor = this.width;
    this.yFactor = this.height;

    this.tree = d3.layout.tree()
        .children(function(d) {
            if (d.solved) { return []; }
            return d.displayedChildren;
        })
        .separation(function(n1, n2) {
            if (self.isCurNodeChild(n1) && self.isCurNodeChild(n2)) { return 1; }
            if (self.isCurNodeGrandChild(n1) && self.isCurNodeGrandChild(n2)) { return 1; }
            return 1;
        })
    ;

    this.div = anchor
        .insert("div", ":first-child")
        .attr("id", "pt-" + this.svgId)
/*
        .on("click", function() {
            // TODO: suspend the activeProofTree
            makeActive(self);
        })
*/
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
        .attr("id", "viewport") // for SVGPan
        .attr("class", "canvas")
    // an okay approximation of the canvas initial translation
        .attr("transform",
              "translate("
              + this.width / maxVisibleNodesOnLine
              + ", "
              + 0
              + ")"
             )
    ;

    this.context =
        this.svg
        .append("g")
        .attr("class", "context")
    // disabled for now
        .style("display", "none")
    ;

    var contextWidth = (this.width - tacticNodeWidth) / 2 - nodeMinSpacing;
    var contextHeight;

    this.context
        .append("foreignObject")
        .attr('x', rectMargin.left)
        .attr("width", contextWidth - rectMargin.left - rectMargin.right)
        .append("xhtml:body")
        .style("background-color", "rgba(0, 0, 0, 0)")
        .html('<div class="node"><p>Empty context</p></div>')
    // now retrieve the computed height of the div
        .attr("height", function() {
            contextHeight = this.firstChild.getBoundingClientRect().height;
            return contextHeight;
        })
    ;

    this.context
        .insert("rect", ":first-child")
        .attr("width", contextWidth)
        .attr("height", contextHeight)
    ;

    this.debug =
        this.svg
        .append("g")
        .attr("class", "debug")
    ;

    var debugWidth = (this.width - tacticNodeWidth) / 2 - nodeMinSpacing;
    var debugHeight;

    this.debug
        .append("foreignObject")
        .attr('x', this.width - debugWidth + rectMargin.left)
        .attr("width", debugWidth - rectMargin.left - rectMargin.right)
        .append("xhtml:body")
        .style("background-color", "rgba(0, 0, 0, 0)")
        .html('<div class="node"><p>No debug information</p></div>')
        .attr("height", function() {
            debugHeight = this.firstChild.getBoundingClientRect().height
            return debugHeight;
        })
    ;

    this.debug
        .insert("rect", ":first-child")
        .attr("x", this.width - debugWidth)
        .attr("width", debugWidth)
        .attr("height", debugHeight)
    ;

    this.svg
        .insert("script", ":first-child")
        .attr("xlink:href", this.roosterDir + "SVGPan.js")
    ;

}

PT.ProofTree = ProofTree;

PT.handleKeyboard = function() {
    d3.select("body")
/*
        .on("click", function() {
            if($(":focus").size() > 0) {
                activeProofTree = undefined;
            }
        })
*/
        .on("keydown", keydownDispatcher)
    ;
}

function nbDisplayedChildren(d) {
    return isGoal(d) ? nbVisibleTactics : nbVisibleGoals;
}

function nbVisibleChildren(d) {
    return isGoal(d) ? nbVisibleTactics : nbVisibleGoals;
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
    if (isTactic(d)) { return tacticNodeWidth; }
    return (this.isRootNode(d))
        ? this.rootNodeWidth
        : this.bottomNodeWidth
    ;
}

function treeDepth(root) {
    return (root.displayedChildren.length > 0)
        ? 1 + _(root.displayedChildren).map(treeDepth).max()
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
              + this.width / maxVisibleNodesOnLine
              + ", "
              + 0
              + ")"
             )
    ;

    this.rootNode = undefined; // will be reset in hInit callback, prevents stale uses

    var success = false;

    this.syncQuery(theorem, function(response) {
        success = self.hInit(response, preAnimCallback, postAnimCallback);
    });

    return success;

}

function mkNode(parent, name, pName, moreFields) {
    return $.extend(
        {
            "id": _.uniqueId(),
            "name": name,
            "pName": pName, // for debugging purposes
            // we preemptively fill the parent and depth fields because d3 will only fill
            // them for the visible nodes of the tree, while some algorithms require it
            // before a node has ever been visible
            "parent": parent,
            "depth": parent.depth + 1,
            "offset": 0,
            "solved": false,
        },
        moreFields
    );
}

function mkGoalNode(parent, g, ndx) {
    return mkNode(
        parent,
        g.gGoal,
        showTermText(g.gGoal),
        {
            "hyps": g.gHyps,
            "ndx": ndx + 1,
            "gid": g.gId,
            "displayedChildren": [], // will be filled later
        }
    );
}

function mkTacticNode(depth, tactic, goals) {

    var n = mkNode(parent, tactic, tactic);

    var children = _(goals)
        .map(_.partial(mkGoalNode, n))
        .value()
    ;

    return $.extend(
        n,
        {
            "allChildren": children,
            "displayedChildren": children.slice(0, nbDisplayedGoals),
            "terminating": _(children).isEmpty(),
        }
    );

}

ProofTree.prototype.runTactic = function(t) {

    var self = this;

    var unfocusedBefore;

    this.syncQueryUndo('idtac.', function(response) {
        unfocusedBefore = response.rGoals.unfocused;
    });

    var newChild;

    self.syncQueryUndo(t, function(response) {
        if(isGood(response)) {
            // if it did not solve the goal
            if (_.isEqual(response.rGoals.unfocused, unfocusedBefore)) {
                newChild = mkTacticNode(self.curNode, t, response.rGoals.focused);
            } else {
                newChild = mkTacticNode(self.curNode, t, []);
            }
        }
    });

    self.curNode.allChildren.unshift(newChild);

    return newChild;

}

ProofTree.prototype.tryAllTactics = function() {

    var self = this;

    var res = [];
    var unfocusedBefore;

    this.syncQueryUndo('idtac.', function(response) {
        unfocusedBefore = response.rGoals.unfocused;
        // preemptively put idtac so that it cancels tactics that do nothing by
        // duplication. eventually it will be removed since it does nothing.
        res.push(mkTacticNode(self.curNode, 'idtac.', response.rGoals.focused));
    });

    var run = function(t) {
        self.syncQueryUndo(t + '.', function(response) {
            if(isGood(response)) {
                // if the tactic did not finish the goal
                if (_.isEqual(response.rGoals.unfocused, unfocusedBefore)) {
                    res.push(mkTacticNode(self.curNode, t + '.', response.rGoals.focused));
                } else { // this tactic proved that goal
                    res.push(mkTacticNode(self.curNode, t + '.', []));
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
        case "inversion":
            _(curHyps).each(function(h) {
                run('inversion ' + h.hName);
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

        this.onError(this, response.rResponse.contents);

/*
        this.error.text(response.rResponse.contents);
        this.svg.style("display", "none");
        this.proofDiv.style("display", "none");
        this.error.style("display", "");
*/

        return false;
    }
    this.error.style("display", "none");

    // There should only be one goal at that point
    this.rootNode = {
        "id": _.uniqueId(),
        "name": response.rGoals.focused[0].gGoal,
        "pName": showTermText(response.rGoals.focused[0].gGoal),
        "x0": 0.5,
        "y0": 0,
        "allChildren": [], // will be filled once this.curNode is set
        "ndx": 1,
        "depth": 0, // need to set depth for isGoal() to work early
        "offset": 0,
        "hyps": [],
        "displayedChildren": [], // will be filled after allChildren is computed
    };

    this.curNode = this.rootNode;

    this.rootNode.allChildren = this.tryAllTactics();
    this.rootNode.displayedChildren = this.rootNode.allChildren.slice(0, nbDisplayedTactics);

    this.update(this.rootNode);

    preAnimCallback(self);

    window.setTimeout(function() { postAnimCallback(self); }, animationDuration);

    return true;

}

function hasParent(n) {
    return n.hasOwnProperty('parent');
}
PT.hasParent = hasParent;

function hasGrandParent(n) {
    return n.hasOwnProperty('parent')
        && n.parent.hasOwnProperty('parent');
}
PT.hasGrandParent = hasGrandParent;

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

ProofTree.prototype.isCurNodeAncestor = function(n) {
    var common = this.commonAncestor(this.curNode, n);
    return common.id === n.id;
}

function getVisibleChildren(n) {
    return n.displayedChildren.slice(n.offset, n.offset + nbVisibleChildren(n));
}

function getVisibleGrandChildren(n) {
    return _(getVisibleChildren(n))
        .map(getVisibleChildren)
        .flatten()
        .value()
    ;
}

ProofTree.prototype.update = function(source, callback) {
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
        .on("click", function(d) {
            self.click(d)
        })
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
            var fo = d3.select(this);

            // TODO: this jquery/d3 business is ugly, fix it somehow
            self.computeDiff(fo, jQDiv, d);

        })
    ;

    node
        .select(".ctxt")
        .style("display", function(d) {
            return self.isCurNode(d) ? "" : "none";
        })
    ;

    node
        .select(".diff")
        .style("display", function(d) {
            return self.isCurNode(d) ? "none" : "";
        })
    ;

    // now we need to update the foreignObject height (it changes depending on whether the
    // context or the diff is displayed)
    node
        .selectAll(function() {
            return this.getElementsByTagName("foreignObject");
        })
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

    // compute the new visible nodes, determine the translation and zoom

    var visibleChildren = _(getVisibleChildren(curNode));
    var visibleGrandChildren = _(getVisibleGrandChildren(curNode));
    var visibleNodes = _([]);
    if (hasParent(curNode)) {
        visibleNodes = visibleNodes.concat(curNode.parent);
    }
    visibleNodes = visibleNodes.concat([curNode]);
    visibleNodes = visibleNodes.concat(visibleChildren.value());
    visibleNodes = visibleNodes.concat(visibleGrandChildren.value());

    var displayedChildren = _(curNode.displayedChildren);
    var displayedGrandChildren = _(displayedChildren)
        .map(function(c) {
            if (c.hasOwnProperty('displayedChildren')) {
                return _(c.displayedChildren).value();
            }
            return [];
        })
        .flatten()
    ;
    var displayedNodes = _([]);
    if (hasParent(curNode)) {
        displayedNodes = displayedNodes.concat(curNode.parent);
    }
    displayedNodes = displayedNodes.concat([curNode]);
    displayedNodes = displayedNodes.concat(displayedChildren.value());
    displayedNodes = displayedNodes.concat(displayedGrandChildren.value());

    var allChildren = _(curNode.allChildren);
    var allGrandChildren = _(allChildren)
        .map(function(c) {
            if (c.hasOwnProperty('allChildren')) {
                return c.allChildren;
            }
            return [];
        })
        .flatten()
    ;

    var firstVisibleChild = visibleChildren.first();
    var lastVisibleChild = visibleChildren.last();
    var firstVisibleGrandChild = visibleGrandChildren.first();
    var lastVisibleGrandChild = visibleGrandChildren.last();

    var minX = visibleNodes
        .map(function(d) { return d.x; })
        .min()
        .value();

    var maxX = visibleNodes
        .map(function(d) { return d.x; })
        .max()
        .value();

    // We want the current node to stay fixed as we scroll through
    // its children, so we always center the viewpoint around it

    var leftdX = curNode.x - minX;
    var rightdX = maxX - curNode.x;
    var halfdX = Math.max(leftdX, rightdX);
    // now recompute the minX, maxX
    minX = curNode.x - halfdX;
    maxX = curNode.x + halfdX;
    var minY = visibleNodes
        .map(function(d) { return d.y; })
        .min()
        .value()
    ;
    var maxY = visibleNodes
        .map(function(d) { return d.y; })
        .max()
        .value()
    ;
    var dX = maxX - minX;
    var dY = maxY - minY;

    var firstChild = allChildren.first();
    var lastChild = allChildren.last();
    var firstGrandChild = allGrandChildren.first();
    var lastGrandChild = allGrandChildren.last();

    var firstDisplayedChild = displayedChildren.first();
    var lastDisplayedChild = displayedChildren.last();

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
        ? _.zip(displayedGrandChildren.value(), displayedGrandChildren.rest().value())
        : [] // because grand-children don't appear for tactic nodes
    ;
    gcSiblings.pop(); // removes [gc_last, undefined] at the end
    var cSiblings = _.zip(displayedChildren.value(), displayedChildren.rest().value());
    cSiblings.pop(); // removes [c_last, undefined] at the end
    var siblings = gcSiblings.concat(cSiblings);

    var siblingsDistances = siblings.map(function(e) {
        return (e[1].x - e[0].x);
    });

    var siblingMinDistance = _.min(siblingsDistances);

    this.xFactor = (siblingMinDistance === Infinity)
        ? this.xFactor
        : (
            ((this.width + nodeMinSpacing) / maxVisibleNodesOnLine)
                / siblingMinDistance
        )
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
    // x and y coordinates, as well as width and height will be set later
        .attr("rx", function(d) {
            return isTactic(d) ? tacticNodeRounding : goalNodeRounding;
        })
        .attr("ry", function(d) {
            return isTactic(d) ? tacticNodeRounding : goalNodeRounding;
        })
        .attr("stroke-width", nodeStroke)
    ;

    // these two need to be updated for all rects, as they change height when displaying
    // context or diff
    node
        .selectAll("rect")
        .attr("y", function(d) {
            return this.nextSibling.getBBox().y - d.height / 2;
        })
        .attr("height", function(n) {
            var h = rectMargin.top
                + this.nextSibling.getBBox().height
                + rectMargin.bottom;
            return h - nodeStroke;
        })
    ;

    gs
        .append("text")
        .attr('class', 'leftarrow')
        .text('←')
        .attr("x", function() {
            var pb = this.parentElement.getBBox();
            return pb.x + pb.width / 2 - 40;
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
            var pb = this.parentElement.getBBox();
            return pb.x + pb.width / 2 + 14;
        })
        .on('click', function(n) {
            self.shiftRight(n);
            d3.event.stopPropagation();
        })
    ;

    node
        .selectAll('text.leftarrow')
    // update y coordinates for all since it changes for current node
        .attr("y", function() {
            var pb = this.parentElement.firstChild.getBBox();
            return pb.y + pb.height + 26;
        })
        .classed('invisible', function(d) {
            return !(
                // visible when:
                !d.solved
                    && d.offset > 0
                    && (self.isCurNode(d) || self.isCurNodeChild(d))
                    && !_.isEmpty(d.displayedChildren)
            );
        })
    ;

    node
        .selectAll('text.rightarrow')
    // update y coordinates for all since it changes for current node
        .attr("y", function() {
            var pb = this.parentElement.firstChild.getBBox();
            return pb.y + pb.height + 26;
        })
        .classed('invisible', function(d) {
            return !(
                // visible when:
                ! d.solved
                    && d.offset + nbVisibleChildren(d) < _(d.allChildren).size()
                    && (self.isCurNode(d) || self.isCurNodeChild(d))
                    && !_.isEmpty(d.displayedChildren)
            );
        })
    ;

    // We want
    // (firstVisibleGrandChild.cX + lastVisibleGrandChild.cX) / 2 = curNode.cX
    // We offset all the descendants to achieve this
    var xMiddle;
    if (firstVisibleGrandChild !== undefined && lastVisibleGrandChild !== undefined) {
        xMiddle = (firstVisibleGrandChild.x + lastVisibleGrandChild.x) / 2;
    } else if (firstVisibleChild !== undefined && lastVisibleChild !== undefined) {
        xMiddle = (firstVisibleChild.x + lastVisibleChild.x) / 2;
    } else {
        xMiddle = curNode.x;
    }

    var descendantsXOffset = curNode.x - xMiddle;

    _(nodes)
        .each(function(n) {
            if (self.isCurNodeGrandChild(n)) {
                n.cX = (n.x + descendantsXOffset) * self.xFactor;
            } else if (self.isCurNodeChild(n)) {
                var grandChildren = _(getVisibleChildren(n));
                if (grandChildren.isEmpty()) {
                    n.cX = (n.x + descendantsXOffset) * self.xFactor;
                } else {
                    var first = grandChildren.first();
                    var last = grandChildren.last();
                    n.cX = ((first.x + last.x) / 2 + descendantsXOffset) * self.xFactor;
                }
            } else if (self.isCurNodeSibling(n)) {
                var smallBigDelta = self.rootNodeWidth - self.bottomNodeWidth;
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
                      : (bottomNodeWidth / 2 - minX * xFactor)
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

    // disabled for now
    //this.updateContext();

    this.updateDebug();

    this.animationRunning = true;
    window.setTimeout(function() {
        self.animationRunning = false;
        if (callback !== undefined) {
            callback();
        }
    }, animationDuration);

}

ProofTree.prototype.updateDisplayedChildren = function(n) {
    if (isGoal(n)) {
        if (nbDisplayedTactics !== +Infinity) {
            n.displayedChildren = n.allChildren.slice(n.offset, n.offset + nbDisplayedTactics);
        } else {
            n.displayedChildren = n.allChildren;
        }
    } else { // isTactic(n)
        if (nbDisplayedGoals !== +Infinity) {
            n.displayedChildren = n.allChildren.slice(n.offset, n.offset + nbDisplayedGoals);
        } else {
            n.displayedChildren = n.allChildren;
        }
    }
}

ProofTree.prototype.shiftLeft = function(n) {
    if (n.solved) { return; }
    if (n.offset > 0) {
        n.offset--;
        this.updateDisplayedChildren(n);
    }
    this.update(n);
}

ProofTree.prototype.shiftRight = function(n) {
    if (n.solved) { return; }
    if (n.offset + nbVisibleChildren(n) < n.allChildren.length) {
        n.offset++;
        this.updateDisplayedChildren(n);
    }
    this.update(n);
}

ProofTree.prototype.click = function(d, remember, callback) {

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

    // when the user clicks on the parent tactic, bring them back to its parent
    if(isTactic(d) && d.depth < this.curNode.depth) {
        this.click(d.parent);
        return;
    }

    this.navigateTo(d, remember);

    if (_.isEmpty(d.allChildren)) {
        if (isGoal(d)) {
            d.allChildren = this.tryAllTactics();
            d.displayedChildren = d.allChildren.slice(0, nbDisplayedTactics);
        }
        // otherwise, this is a terminating tactic for this goal!
        else {
            this.solved(d);
        }
    }

    this.expand(d);
    this.update(d, callback);

}

// called when n has been solved
ProofTree.prototype.solved = function(n) {

    var self = this;
    n.solved = true;
    n.displayedChildren = [];
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

function collapse(d) {
    if (d.displayedChildren) {
        d.displayedChildren = [];
    }
}

function collapseChildren(d) {
    _(d.displayedChildren)
        .forEach(function(n) {
            collapse(n);
        })
    ;
}

function collapseExcept(d, e) {
    if (d.displayedChildren) {
        d.displayedChildren = [e];
    }
}

ProofTree.prototype.expand = function(d) {
    var self = this;
    this.updateDisplayedChildren(d);
    if (isGoal(d)) {
        _(d.displayedChildren)
            .each(self.updateDisplayedChildren.bind(self));
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

function hasDisplayedChild(n) {
    return (n.displayedChildren && n.displayedChildren[0]) ? true : false;
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

ProofTree.prototype.navigateTo = function(dest, remember) {

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

                if (remember) {
                    src.partial = dst;
                } else {
                    delete src["partial"];
                }

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
                    self.expand(src);
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

function getBinder(t) {
    return t[0];
}

function getBinders(t) {
    if (_.isEmpty(t)) { return []; }
    return _.union(getBinder(t[0]), getBinders(_(t).rest().value()));
}

ProofTree.prototype.makeContextDiv = function(goal) {

    var jContextDiv = $("<div>");

    var hypsLookup = {};
    _(goal.hyps)
        .each(function(h) {
            hypsLookup[h.hName] = showTermText(h.hType);
        })
    ;

    /*
      adding to the context only those variables that are not referred to in the
      type of others. those referred to will have their type in tooltips
      wherever they are mentioned.
      we collect such references by processing the hypotheses from the back.
     */
    var seen = [];
    _(goal.hyps).forEachRight(function(h) {
        if (!_(seen).contains(h.hName)) {
            var p = $("<p>");
            p.append($("<span>").text(h.hName + " : "));

            var annotateTerm = function(t, boundVars) {
                var c = t.contents;
                switch (t.tag) {

                case "Var":
                    if (boundVars[c] === undefined && hypsLookup[c] !== undefined) {
                        t.type = hypsLookup[c];
                        seen.push(c);
                    }
                    break;

                case "Forall":
                    var newBound = getBinders(c[0]);
                    annotateTerm(c[1], _.union(newBound, boundVars));
                    break;

                case "Arrow":
                    annotateTerm(c[0], boundVars);
                    annotateTerm(c[1], boundVars);
                    break;

                case "App":
                    annotateTerm(c[0], boundVars);
                    annotateTerm(c[1], boundVars);
                    break;

                default:
                    alert("UNKNOWN TAG");
                    break;

                };
            }

            var hTypeCopy = $.extend(true, {}, h.hType);
            annotateTerm(hTypeCopy, []);
            p.append(
                $("<span>")
                    .html(showTermInline(hTypeCopy))
            );

            jContextDiv.prepend(p);
        }
    });

    return jContextDiv;

}

// TODO: this should use d3 data binding rather than manual management...
ProofTree.prototype.updateContext = function(d3ContextDiv) {

    var contextDiv = this.context.select('div');
    var jContextDiv = $(contextDiv[0]);

    contextDiv.style("display", this.isCurNode(this.rootNode) ? "none" : "");

    var curGoal = (isGoal(this.curNode)) ? this.curNode : this.curNode.parent;
    var hypsLookup = {};
    _(curGoal.hyps)
        .each(function(h) {
            hypsLookup[h.hName] = showTermText(h.hType);
        })
    ;

    jContextDiv.empty();
    var curGoal = (isGoal(this.curNode)) ? this.curNode : this.curNode.parent;
    jContextDiv.append(this.makeContextDiv(curGoal));

    if (jContextDiv.html() === "") {
        jContextDiv.append("p").text("Empty context");
    }

    updateNodeHeight(this.context);

}

ProofTree.prototype.updateDebug = function() {

    var debugDiv = this.debug.select('div');
    var jDebugDiv = $(debugDiv[0]);

    debugDiv.style("display", ((this.isCurNode(this.rootNode)) ? "none" : ""));

    var partialProof = this.partialProofFrom(this.rootNode, 1);

    jDebugDiv.empty();
    jDebugDiv.append($("<div>").text(this.theorem));
    jDebugDiv.append($("<div>").text("Proof."));
    partialProof.prepend(span("&nbsp;&nbsp;")); // initial indentation
    jDebugDiv.append(partialProof);
    //$(".resizeWidth, .resizeHeight").change();
    jDebugDiv.append($("<div>").text("Qed."));

/*
    if (response.rGoals.focused.length > 0) {
        debugDiv.html(showTerm(response.rGoals.focused[0].gGoal));
    } else {
        debugDiv.html(response.rResponse.contents[0]);
    }
*/

    updateNodeHeight(this.debug);

}

function keydownDispatcher() {
    if (activeProofTree !== undefined) {
        activeProofTree.keydownHandler.call(activeProofTree);
    }
}

ProofTree.prototype.keydownHandler = function() {

    // don't interact while typing
    if (d3.event.target.type === "textarea") { return; }

    var curNode = this.curNode;

    var visibleChildren = getVisibleChildren(curNode);

    if (this.animationRunning) {
        // all keys are frozen during animation
        d3.event.preventDefault();
        return;
    }

    switch (d3.event.keyCode) {

    case 37: // Left
    case 65: // a
        this.shiftLeft(curNode);
        break;

    case 39: // Right
    case 68: // d
        this.shiftRight(curNode);
        break;

    case 38: // Up
    case 87: // w
        if(hasParent(curNode)) {
            this.click(curNode.parent);
        }
        break;

    case 40: // Down
    case 83: // s
        if (isTactic(curNode)) {
            var dest = _(visibleChildren).find(function(n) {
                return !n.solved;
            });
            if (dest !== undefined) { this.click(dest); }
        } else {
            if (visibleChildren.length > 0) {
                this.click(visibleChildren[0]);
            }
        }
        break;

    case 49: case 97: // 1, K1
        if (visibleChildren.length > 0) {
            this.click(visibleChildren[0]);
        }
        break;

    case 50: case 98: // 2, K2
        if (visibleChildren.length > 1) {
            this.click(visibleChildren[1]);
        }
        break;

    case 51: case 99: // 3, K3
        if (visibleChildren.length > 2) {
            this.click(visibleChildren[2]);
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

function span(t) {
    return $("<span>")
        .css("vertical-align", "top")
        .html(t)
    ;
}

// returns a jQuery HTML partial proof
ProofTree.prototype.partialProofFrom = function(t, indentation) {

    var self = this;
    var indent = repeat(2 * indentation, "&nbsp;");

    if (isGoal(t)) {
        // if one of the subgoals is solved, find it and return its proof
        var solution = _(t.allChildren).find("solved");
        if (solution !== undefined) {
            return this.partialProofFrom(solution, indentation);
        }
        // try to see if a partial path was recorded
        var partial = _(t.allChildren).find(function(n) {
            return n.hasOwnProperty("partial");
        });
        if (partial !== undefined) {
            return this.partialProofFrom(partial, indentation);
        }
        // otherwise, try to find a node in the ancestor tree of the current
        var curTac = _(t.allChildren).find(function(n) {
            return self.isCurNodeAncestor(n);
        });
        if (curTac !== undefined) {
            return this.partialProofFrom(curTac, indentation);
        }
        if (this.isCurNode(t)) {
            var result = $("<span>");
            var ta = $("<textarea>")
                .addClass("resizeWidth")
                .addClass("resizeHeight")
                .addClass("activeTextarea")
                .css("background-color", "#77DD77")
                .css("resize", "none")
            ;
            PT.resizeTextarea.call(ta);
            result.append(ta);
            result.append(
                $("<button>")
                    .css("margin", 0)
                    .css("padding", "0px 2px")
                    .css("border", 0)
                    .css("background-color", "#FFB347")
                    .css("vertical-align", "top")
                    .text("OK")
                    .click(function() {

                        var tactic = ta.val();
                        // if the tactic is already here, just click it
                        var existingTactic = _(self.curNode.allChildren).find(function(elt) {
                            return elt.name === tactic;
                        });

                        if (existingTactic !== undefined) {
                            console.log(existingTactic);
                            self.click(existingTactic);
                            return;
                        }

                        // this adds the node but does not update the display
                        var newNode = self.runTactic(tactic);

                        // now we can update and click on the node once it has appeared
                        self.update(self.curNode, function() {
                            self.click(newNode);
                        });

                    })
            );
            return result;
        } else {
            var ta = $("<textarea>")
                .addClass("resizeWidth")
                .addClass("resizeHeight")
                .val("admit.")
                .css("resize", "none")
                .focus(function() {
                    self.click(
                        t,
                        true,
                        function() {
                            var ta = $(".activeTextarea");
                            $(".activeTextarea").focus();
                        }
                    );
                })
            ;
            PT.resizeTextarea.call(ta);
            return ta;
        }
    }
    else {
        var result = span(t.name);
        if (t.allChildren.length == 1) {
            _(t.allChildren).each(function(e) {
                result.append(document.createTextNode(" "));
                result.append(self.partialProofFrom(e, indentation));
            });
        } else {
            _(t.allChildren).each(function(e) {
                var subproof = $("<div>");
                subproof.append(span(indent + "{&nbsp;"));
                subproof.append(
                    $("<span>").append(self.partialProofFrom(e, indentation + 1))
                );
                // should be div if the proof has branching
                subproof.append(span(" }"));
                result.append(subproof);
            });
        }
        return result;
    }

}

// returns a text proof
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

function hasBranching(proof) {
    if (_.isEmpty(proof)) { return false; }
    if (_(proof[1]).size() > 1) { return true }
    return hasBranching(proof[1][0]);
}

PT.pprintAux = function(proof, indentation) {

    if (_.isEmpty(proof)) { return ""; }

    var fst = proof[0];
    var snd = proof[1];
    var indent = repeat(2 * indentation, "&nbsp;");

    //if (fst === "todo.") { fst = '<span style="color: green;">admit.</span>'; }

    if (_.isEmpty(snd)) { return fst; }

    if (_(snd).size() === 1) {
        return fst + " "
            + _(snd).reduce(
                function(acc, elt) {
                    return acc + PT.pprintAux(elt, indentation);
                },
                ""
            )
        ;
    }

    return fst
        + _(snd).reduce(
            function(acc, elt) {
                return acc
                    + "<br>" + indent
                    + "{ " + PT.pprintAux(elt, indentation + 1)
                    + (hasBranching(elt) ? "<br>" + indent + "}" : " }")
                ;
            },
            ""
        )
    ;

}

PT.pprint = function(proof, indentation) {
    return repeat(2 * indentation, "&nbsp;") + PT.pprintAux(proof, indentation);
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

    var self = this;

    if (!_.isEmpty(proof)) {
        var fst = proof[0];
        var snd = proof[1];
        this.syncQuery(fst, function(response) {
            if (isGood(response)) {
                _(snd).each(function(n) {
                    self.replayThisProof(self.proofFrom(n));
                });
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
                + "<br>Qed."
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
    return showNames(t[0]) + syntax(":") + nbsp + showTermAux(t[1], 0, 0, false);
}

function showNames(t) {
    if (_.isEmpty(t)) { return ""; }
    return ident(t[0]) + " " + showNames(_(t).rest().value());
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
var precAnd    = precedence++; var precOr = precAnd;
var precEqual  = precedence++; var precNotEqual = precEqual;
var precAndB   = precedence++; var precOrB = precAndB;
var precPlus   = precedence++; var precMinus = precPlus;
var precMult   = precedence++;
var precApp    = precedence++;

var nbsp = "&nbsp;";
function vernac(s) { return '<span class="vernac">' + s + '</span>'; }
function syntax(s) { return '<span class="syntax">' + s + '</span>'; }
function ident(s) { return '<span class="identifier">' + s + '</span>'; }
function term(s) { return '<span class="term">' + s + '</span>'; }

function showConstructor(t) {
    var name = t[0];
    if (t[1] === null) {
        return syntax("|")
            + nbsp
            + ident(name)
        ;
    } else {
        var type = showTermInline(t[1]);
        return syntax("|")
            + nbsp
            + ident(name)
            + nbsp
            + syntax(":")
            + nbsp
            + type
        ;
    }
}

function showVernac(t) {
    var c = t.contents;

    switch (t.tag) {

    case "Inductive":
        var name = c[0];
        var type = showTermInline(c[1]);
        var constructors = _(c[2]).map(showConstructor);
        return vernac("Inductive")
            + nbsp
            + ident(name)
            + nbsp
            + syntax(":")
            + nbsp
            + type
            + nbsp
            + syntax(":=")
            + "<br>"
            + _(constructors).reduce(function(acc, elt) { return acc + elt + "<br>"; }, "")
            + syntax(".")
        ;

    case "Theorem":
        var name = c[0];
        var type = showTermInline(c[1]);
        return vernac("Theorem")
            + nbsp
            + ident(name)
            + nbsp
            + syntax(":")
            + nbsp
            + type
            + syntax(".")
        ;

    default:
        return "Unknown Vernacular tag: " + t.tag;

    };
}

function showTermText(t) {
    return $(showTermInline(t)).text();
}

function showTermAux(t, indentation, precParent, newline) {
    var c = t.contents;

    var indent = getIndent(indentation);

    var par = function(precOp, text) {
        if (precOp <= precParent) {
            return term("(" + text + ")");
        } else {
            return term(text);
        }
    };

    var showOp = function(c, op, precOp) {
        return par(
            precOp,
            showTermAux(c[0].contents[1], 0, precOp, false)
                + " " + syntax(op) + " "
                + showTermAux(c[1], 0, precOp, false)
        );
    };

    switch (t.tag) {

    case "Var":
        if (t.type !== undefined) {
            return '<span style="font-weight: bold;"'
                + ' title="' + t.type + '">'
                + c + '</span>'
            ;
        } else {
            return term(c);
        }

    case "Forall":
        return par(
            precForall,
            syntax("∀") + nbsp + showBinders(c[0]) + syntax(",")
                + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
                + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Arrow":
        return term(
            showTermAux(c[0], indentation, precArrow, false)
                + nbsp + syntax("→") + (newline ? "<br/>" + indent : " ")
                + showTermAux(c[1], indentation, precParent, newline)
        );

    case "App":

        // handling special case of infix operators I want to pretty print
        if (c[0].contents === "not"
            && c[1].contents[0].contents[0].contents === "eq"
           ) {
            return par(
                precNotEqual,
                showTermAux(c[1].contents[0].contents[1], 0, precNotEqual, false)
                    + " ≠ "
                    + showTermAux(c[1].contents[1], 0, precNotEqual, false)
            )
        }

        if (c[0].tag === "App") {
            switch (c[0].contents[0].contents) {

            case "eq":
                return showOp(c, "=", precEqual);

            case "plus":
                return showOp(c, "+", precPlus);

            case "minus":
                return showOp(c, "-", precMinus);

            case "mult":
                return showOp(c, "*", precMult);

            case "and":
                return showOp(c, "∧", precAnd);

            case "or":
                return showOp(c, "∨", precOr);

            case "andb":
                return showOp(c, "&&", precAndB);

            case "orb":
                return showOp(c, "||", precOrB);

            default:
                console.log("Falling through", c[0].contents[0].contents);
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
    var res = term(h.hName);
    if (h.hValue !== null) {
        res = res + nbsp + syntax(":=") + nbsp + showTermInline(h.hValue);
    }
    res = res + nbsp + syntax(":") + nbsp + showTermInline(h.hType);
    return res;
}
PT.showHypothesis = showHypothesis;

function showTermInline(t) {
    return showTermAux(t, 0, 0, false);
}

function computeDiffOldWay(fo, jQDiv, d) {

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

}

function mkDiff(oldArray, newArray) {
    var removed = [], changed = [], added = [];

    var oldHyps = {};
    _(oldArray).each(function(h) { oldHyps[h.hName] = h; });

    var newHyps = {};
    _(newArray).each(function(h) { newHyps[h.hName] = h; });

    for (var o in oldHyps) {
        if (newHyps.hasOwnProperty(o)) {
            changed.push({
                "before": oldHyps[o],
                "after": newHyps[o],
            });
        } else {
            removed.push(oldHyps[o]);
        }
    }

    for (var n in newHyps) {
        if (oldHyps.hasOwnProperty(n)) {
            // nothing, already done
        } else {
            added.push(newHyps[n]);
        }
    }

    return {
        "removed": removed,
        "changed": changed,
        "added": added,
    };
}

function spotTheDifferences(before, after) {

    var nbBefore = before.children().length;
    var nbAfter  =  after.children().length;
    if (nbBefore !== nbAfter) {
        before.addClass("removed");
        after.addClass("added");
        return;
    }

    var nbChildren = nbBefore;
    if (nbChildren === 0) { // both leaves
        if (before.html() !== after.html()) {
            before.addClass("removed");
            after.addClass("added");
        }
        return;
    }

    for (var i in _.range(nbChildren)) {
        spotTheDifferences(
            $(before.children()[i]),
            $(after.children()[i])
        );
    }

}

ProofTree.prototype.computeDiff = function(fo, jQDiv, d) {

    if (isGoal(d)) {

        var diffDiv = $("<div>").addClass("diff");
        var contextDiv = $("<div>").addClass("ctxt");
        contextDiv.append(this.makeContextDiv(d));

        jQDiv.append(diffDiv);
        jQDiv.append(contextDiv);

        if (hasGrandParent(d)) {

            var diff = mkDiff(d.parent.parent.hyps, d.hyps);

            var removed = diff.removed, changed = diff.changed, added = diff.added;

            var minusPane = $("<div>").addClass("diff-pane");
            diffDiv.append(minusPane);
            diffDiv.append(
                $("<div>").addClass("diff-pane-sep").text("⇒")
            );
            var plusPane = $("<div>").addClass("diff-pane");
            diffDiv.append(plusPane);

            _(changed).each(function(hs) {
                if (JSON.stringify(hs.before) !== JSON.stringify(hs.after)) {
                    var before = $("<span>").html(showHypothesis(hs.before));
                    minusPane.append(before);
                    minusPane.append($("<br>"));
                    var after = $("<span>").html(showHypothesis(hs.after));
                    plusPane.append(after);
                    plusPane.append($("<br>"));
                    spotTheDifferences(before, after);
                }
            });

            _(removed).each(function(h) {
                minusPane.append($("<span>").addClass("removed").html(showHypothesis(h)));
                minusPane.append($("<br>"));
            });

            _(added).each(function(h) {
                plusPane.append($("<span>").addClass("added").html(showHypothesis(h)));
                plusPane.append($("<br>"));
            });

            if (minusPane.is(':empty') && plusPane.is(':empty')) {
                diffDiv.empty();
            }

            jQDiv.append($('<hr>'));

        } else {

            _(d.hyps).each(function(h) {
                diffDiv.append(
                    $("<span>")
                        .addClass("added")
                        .html('⊕ ' + showHypothesis(h))
                );
            });

            if (!_(d.hyps).isEmpty()) { diffDiv.append($('<hr>')); }

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

}

function setupTextareaResizing() {
    var minimalWidth = 16;
    var minimalHeight = 16;
    var duration = 0;

    var hiddenDiv = $("<div>")
        .css("font-family", "monospace")
        .css("display", "none")
        .css("float", "right") // doesn't disrupt the flow when displayed
    ;

    $("body").append(hiddenDiv);

    PT.resizeTextarea = function() {
        var content = $(this).val();
        hiddenDiv.html(
            content
                .replace(/\n/g, '&nbsp;&nbsp;<br>')
                .replace(/ /g, '&nbsp;')
                + '&nbsp;' // in case the last line is blank
        );
        if ($(this).hasClass("resizeWidth")) {
            $(this).animate(
                {'width': Math.max(hiddenDiv.width() + 2, minimalWidth)},
                duration
            );
        }
        if ($(this).hasClass("resizeHeight")) {
            $(this).animate(
                {'height': Math.max(hiddenDiv.height() + 2, minimalHeight)},
                duration
            );
        }
    };

    $(document)
        .on('change keyup keydown paste', 'textarea', PT.resizeTextarea)
    ;

}

function extractNodeUpToGrandChildren(n) {
    function cleanup(n) {
        delete n["cX0"];
        delete n["cY0"];
        delete n["cX"];
        delete n["cY"];
        delete n["x0"];
        delete n["y0"];
        delete n["x"];
        delete n["y"];
        delete n["gid"];
        delete n["ndx"];
        delete n["children"];
        delete n["displayedChildren"];
        delete n["parent"];
        delete n["solved"];
        delete n["offset"];
        delete n["height"];
    };
    var root = $.extend({}, n);
    var rootChildren = root.allChildren;
    var rootGrandchildren =
        _(root.children)
        .map(function(d) { return d.allChildren; })
        .flatten()
        .value()
    ;
    cleanup(root);
    _(rootChildren).each(cleanup);
    _(rootGrandchildren).each(cleanup);
    _(rootGrandchildren).each(function(e) { e.allChildren = []; })
    return JSON.stringify(root);
}
