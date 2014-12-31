
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
var svgPanEnabled = false;
var nodeVSpacing = 10;
var nodeStroke = 2;
var rectMargin = {top: 2, right: 8, bottom: 2, left: 8};
var animationDuration = 360;
var tacticNodeRounding = 10;
var goalNodeRounding = 0;
$(document).ready(function() {
    $(window).click(function(event) {
        // TODO: this is kinda clunky, but at least we can mark tutorial windows
        // as non-disactivating
        // if the click did not originate in a SVG, disactivate proof trees
        if ($(event.target).closest(".svg").length === 0) {
            activeProofTree = undefined;
        }
    });
    setupTextareaResizing();
});
var diffRed   = "#EE8888";
var diffGreen = "#88EE88";
var diffBlue  = "#8888EE";
var diffOpacity = 0.90;
var redStroke   = diffRed;
var greenStroke = diffGreen;
var blueStroke  = diffBlue;
var goalBodyPadding = 4;

// CHECKS
function assert(condition, message) {
    if (!condition) {
        alert(message);
        throw message || "Assertion failed";
    }
}

// COMPUTED GLOBALS
var activeProofTree;

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
    'split',
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
PT.allTactics = PT.tDiscriminate;

function getAllChildren(n) {
    return n.allChildren;
}

function getAllGrandChildren(n) {
    return _(getAllChildren(n))
        .map(getAllChildren)
        .flatten()
        .value()
    ;
}

ProofTree.prototype.getVisibleChildren = function(d) {
    var self = this;
    if (d.solved) { return []; }
    if (d.collapsed) {
        // if d is collapsed, we only return an ancestor of the current node
        return _(d.allChildren)
            .filter(self.isCurNodeAncestor.bind(self))
            .value()
        ;
    }
    return d.allChildren;
}

ProofTree.prototype.getVisibleGrandChildren = function(d) {
    return _(this.getVisibleChildren(d))
        .map(this.getVisibleChildren.bind(this))
        .flatten()
        .value()
    ;
}

/*
  The following DOM is constructed from the given anchor:

anchor
`- div id="pt-n"
|  `- svg id="svg-n"
|     `- script xhref="SVGPan.js"
|     `- g id="viewport"            pannable and zoomable (SVGPan.js)
|     |  `- g id="link-layer"
|     |  `- g id="rect-layer"
|     |  `- g id="diff-layer"
|     |  `- g id="text-layer"
|     `- context
|     `- debug
`- div id="proof-n"
`- div id="error-n"

*/
// [anchor] is a native DOM element
function ProofTree(anchor, width, height, qedCallback, onError) {

    var self = this;

    this.anchor = d3.select(anchor);
    this.width = width;
    this.height = height;
    this.qedCallback = qedCallback;
    this.onError = onError;

    this.animationRunning = false;
    this.paused = false;
    this.svgId = _.uniqueId();
    this.xFactor = this.width;
    this.yFactor = this.height;
    this.userState = {};
    this.usingKeyboard = false;
    this.goalNodeWidth = Math.floor(this.width/3);
    this.tacticNodeMaxWidth = Math.floor(this.width/6);

    this.tree = d3.layout.tree()
        .children(self.getVisibleChildren.bind(self))
        .separation(function(d) {
            return 1 / (d.depth + 1);
        })
    ;

    this.diagonal = d3.svg
        .diagonal()
        .projection(function(d) { return [d.y, d.x]; })
    ;

    this.div = this.anchor
        .insert("div", ":first-child")
        .attr("id", "pt-" + this.svgId)
    ;

    this.svg = this.div
        .insert("svg", ":first-child")
        .classed("svg", true)
        .attr("id", "svg-" + this.svgId)
        .attr("display", "block") // necessary for the height to be exactly what we set
        .style("width", this.width)
        .style("height", this.height)
        //.attr("focusable", true)
        //.attr("tabindex", 0) // this creates a blue outline that changes the width weirdly
        .on("click", function() {
            activeProofTree = self;
            self.usingKeyboard = false;
        })
    ;

    this.viewport =
        this.svg
        .append("g")
        .attr("id", "viewport") // for SVGPan.js
        .attr("class", "viewport")
        .attr("transform",
              "translate(" + self.goalNodeWidth + ", " + 0 + ")"
             )
    ;

    // Note : the order of these influence the display: first = bottom, last = top
    this.linkLayer = this.viewport.append("g").attr("id", "link-layer");
    this.rectLayer = this.viewport.append("g").attr("id", "rect-layer");
    this.diffLayer = this.viewport.append("g").attr("id", "diff-layer");
    this.textLayer = this.viewport.append("g").attr("id", "text-layer");
    this.tipsLayer = this.viewport.append("g").attr("id", "tips-layer");

    this.debug = this.svg.append("g");

    var debugHeight;

    this.debug
        .append("foreignObject")
        .attr("width", this.width)
        .append("xhtml:body")
        .classed("svg", true)
        .style("background-color", "rgba(0, 0, 0, 0)")
        .style("font-family", "monospace")
        .html('<div class="node"><p>No debug information</p></div>')
        .attr("height", function() {
            debugHeight = this.firstChild.getBoundingClientRect().height
            return debugHeight;
        })
    ;

    this.debug
        .insert("rect", ":first-child")
        .attr("width", this.width)
        .attr("height", debugHeight)
        .attr("fill", "#B2DBA1")
    ;

    if (svgPanEnabled) {
        this.svg
            .insert("script", ":first-child")
            .attr("xlink:href", "SVGPan.js")
        ;
    }

}

ProofTree.prototype.resize = function(width, height) {
    this.width = width;
    this.height = height;
    this.div.style("width", this.width);
    this.div.style("height", this.height);
    this.svg.style("width", this.width);
    this.svg.style("height", this.height);
    this.goalNodeWidth = Math.floor(this.width/3);
    this.tacticNodeMaxWidth = Math.floor(this.width/6);
    this.update();
}

PT.ProofTree = ProofTree;

PT.handleKeyboard = function() {
    d3.select("body")
        .on("keydown", keydownDispatcher)
    ;
}

function avg(n1, n2) { return (n1 + n2) / 2; }

function mkDot(x, y) { return {"x": x, "y": y}; }

function showDot(d) { return d.x + " " + d.y; }

function connectRects(r1, r2, rightsLeft) {
//console.log("rect1", r1, "rect2", r2);
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

    /*
console.log("M", a,
    (
        "M" + showDot(a)
            + "L" + showDot(b)
            + "C" + showDot(cp1) + "," + showDot(cp2) + "," + showDot(c)
            + "L" + showDot(d) + "," + showDot(e) + "," + showDot(f)
            + "C" + showDot(cp3) + "," + showDot(cp4) + "," + showDot(g)
            + "L" + showDot(h)
            + "Z"
    )
);
    */

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

function deltaX(rect1, rect2) { return rect2.left - rect1.left; }
function deltaY(rect1, rect2) { return rect2.top - rect1.top; }

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

function sameNode(n1, n2) { return n1.id === n2.id; }

// creates an empty rectangle in the same column as [node], at vertical position [currentY]
function emptyRect(node, currentY) {
    var delta = 1; // how big to make the empty rectangle
    return $.extend(
        {"left": node.cX, "right": node.cX + node.width, "width": node.width},
        {"top": currentY - delta, "bottom": currentY + delta, "height": 2 * delta}
    );
}

function byNodeId(d) { return d.id; }

function byLinkId(d) { return d.source.id + "," + d.target.id; }

function nodeX(d) { return d.y; }

function nodeY(d) { return d.x; }

ProofTree.prototype.xOffset = function(d) {
    return - d.width / 2; // position the center
}

ProofTree.prototype.yOffset = function(d) {
    var offset = - d.height / 2; // for the center
    if (this.isCurGoalChild(d) || this.isCurGoalGrandChild(d)) {
        return offset + this.descendantsOffset;
    } else {
        return offset;
    }
}

var centerLeftOffset  = +10;

var centerRightOffset = -10;

function centerLeft0(d) { return {"x": d.cX0 + centerLeftOffset, "y": d.cY0 + d.height / 2}; }

function centerRight0(d) {
    return {"x": d.cX0 + d.width + centerRightOffset, "y": d.cY0 + d.height / 2};
}

function centerLeft(d) { return {"x": d.cX + centerLeftOffset, "y": d.cY + d.height / 2}; }

function centerRight(d) {
    return {"x": d.cX + d.width + centerRightOffset, "y": d.cY + d.height / 2};
}

function swapXY(r) { return {"x": r.y, "y": r.x}; }

function parseSVGTransform(a) {
    var b = {};
    for (var i in a = a.match(/(\w+\((\-?\d+\.?\d*,? ?)+\))+/g)) {
        var c = a[i].match(/[\w\.\-]+/g);
        b[c.shift()] = c;
    }
    return b;
}

function SVGTransformX(elt) {
    var t = parseSVGTransform(elt.attr("transform"));
console.log("X after parse", t.translate);
    if (t.hasOwnProperty("matrix")) {
        return + t.matrix[4];
    } else if (t.hasOwnProperty("translate")) {
        return + t.translate[0];
    } else {
        console.log("Could not parse SVG transform", elt, t);
    }
}

function SVGTransformY(elt) {
    var t = parseSVGTransform(elt.attr("transform"));
console.log("Y after parse", t.translate);
    if (t.hasOwnProperty("matrix")) {
        return + t.matrix[5];
    } else if (t.hasOwnProperty("translate")) {
        return + t.translate[1];
    } else {
        console.log("Could not parse SVG transform", elt, t);
    }
}

function evenFloor(x) {
    var r = Math.floor(x);
    return (r % 2 === 0) ? r : r - 1;
}

ProofTree.prototype.newTheorem = function(
    theorem,
    tactics,    // function from prooftree to set of tactics allowed
    afterUpdate, // callback after every update
    afterFirstUpdate // callback after the first update ends
)
{

    var self = this;

    this.theorem = theorem;
    this.tactics = tactics;
    this.afterUpdate = afterUpdate === undefined ? function(){} : afterUpdate;

    // hide previous proof result if any, show svg if hidden
    this.svg.style("display", "");

    this.rootNode = undefined; // will be reset in hInit callback, prevents stale uses

    var success = false;

    syncQuery(theorem, function(response) {
        success = self.hInit(response, afterFirstUpdate);
    });

    syncLogAction("THEOREM " + theorem);

    $(this.svg[0]).focus();
    this.svg.on("click")();

    return success;

}

ProofTree.prototype.newAlreadyStartedTheorem = function(theoremStatement, lastResponse)
{

    var self = this;

    this.theorem = theoremStatement;
    this.tactics = function() { return PT.allTactics; };
    this.afterUpdate = function(){};

    // hide previous proof result if any, show svg if hidden
    this.svg.style("display", "");

    this.rootNode = undefined; // will be reset in hInit callback, prevents stale uses

    var success = false;

    self.hInit(lastResponse, function() {});

    $(this.svg[0]).focus();
    this.svg.on("click")();

    return success;

}

function mkNode(parent, name, pName, moreFields) {
    return $.extend(
        {
            "id": _.uniqueId(),
            "allChildren": [],
            "name": name,
            "pName": pName, // for debugging purposes
            // we preemptively fill the parent and depth fields because d3 will only fill
            // them for the visible nodes of the tree, while some algorithms require it
            // before a node has ever been visible
            "parent": parent,
            "depth": parent.depth + 1,
            "focusIndex": 0,
            "solved": false,
            "collapsed": false, // nodes need to be created uncollapsed so that D3 registers them
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
            "terminating": _(children).isEmpty(),
        }
    );

}

ProofTree.prototype.runTactic = function(t) {

    var self = this;

    var unfocusedBefore;

    syncQueryUndo('idtac.', function(response) {
        unfocusedBefore = response.rGoals.unfocused;
    });

    var newChild;

    syncQueryUndo(t, function(response) {
        if (isGood(response)) {
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

    syncQueryUndo('idtac.', function(response) {
        unfocusedBefore = response.rGoals.unfocused;
        // preemptively put idtac so that it cancels tactics that do nothing by
        // duplication. eventually it will be removed since it does nothing.
        res.push(mkTacticNode(self.curNode, 'idtac.', response.rGoals.focused));
    });

    var run = function(t) {
        syncQueryUndo(t + '.', function(response) {
            if (isGood(response)) {
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

    _(this.tactics(this)).each(function(t) {

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

ProofTree.prototype.hInit = function(response, afterUpdate) {

    var self = this;

    if (isBad(response)) {
        console.log(response.rResponse.contents);

        if (this.onError !== undefined) {
            this.onError(this, response.rResponse.contents);
        }

        return false;
    }

    // There should only be one goal at that point
    this.rootNode = {
        "id": _.uniqueId(),
        "name": response.rGoals.focused[0].gGoal,
        "pName": showTermText(response.rGoals.focused[0].gGoal),
        "x0": 0,
        "y0": 0.5,
        "allChildren": [], // will be filled once this.curNode is set
        "ndx": 1,
        "depth": 0, // need to set depth for isGoal() to work early
        "focusIndex": 0,
        "hyps": [],
        "collapsed": false,
    };

    this.curNode = this.rootNode;

    this.rootNode.allChildren = this.tryAllTactics();

    this.update(afterUpdate);

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

ProofTree.prototype.curGoal = function() {
    return isGoal(this.curNode) ? this.curNode : this.curNode.parent;
}

ProofTree.prototype.isCurGoal = function(n) { return n.id === this.curGoal().id; }

ProofTree.prototype.isCurGoalChild = function(n) {
    return hasParent(n) && this.isCurGoal(n.parent);
}

ProofTree.prototype.isCurGoalGrandChild = function(n) {
    return hasParent(n) && this.isCurGoalChild(n.parent);
}

ProofTree.prototype.isRootNode = function(n) { return n.id === this.rootNode.id; }

ProofTree.prototype.isCurNode = function(n) { return n.id === this.curNode.id; }

ProofTree.prototype.isCurNodeParent = function(n) {
    return hasParent(this.curNode) && this.curNode.parent.id === n.id;
}

ProofTree.prototype.isCurNodeChild = function(n) {
    return hasParent(n) && this.isCurNode(n.parent);
}

ProofTree.prototype.isCurNodeGrandChild = function(n) {
    return hasParent(n) && this.isCurNodeChild(n.parent);
}

ProofTree.prototype.isCurNodeSibling = function(n) {
    return !this.isCurNode(n) && hasParent(n) && this.isCurNodeParent(n.parent);
}

ProofTree.prototype.isCurNodeAncestor = function(n) {
    var common = this.commonAncestor(this.curNode, n);
    return common.id === n.id;
}

ProofTree.prototype.resetSVGTransform = function() {
    var m = parseSVGTransform(this.viewport.attr('transform'));
    if (m.hasOwnProperty('matrix')) {
        m = m.matrix;
        this.viewport.attr('transform',
                    'matrix(1' + ',' + m[1] + ',' + m[2]
                    + ', 1' + ',' + m[4] + ',' + m[5] +')')
        ;
    }
}

ProofTree.prototype.linkWidth = function(d) {
    var src = d.source;
    var tgt = d.target;
    var thin = "2px";
    var thick = "5px";
    // if the user uses his mouse, highlight the path under hover
    if (!this.usingKeyboard) {
        if (this.hoveredNode === undefined) {
            return thin;
        } else {
            if (this.isCurNode(src)) {
                if (sameNode(tgt, this.hoveredNode)) { return thick; }
                else if (!hasParent(this.hoveredNode)) { return thin; }
                else if (sameNode(tgt, this.hoveredNode.parent)) { return thick; }
                else { return thin; }
            } else if (this.isCurNodeChild(src)) {
                if (sameNode(tgt, this.hoveredNode)) { return thick; }
                else { return thin; }
            } else {
                return thin;
            }
        }
    }
    // if the user uses his keyboard, highlight the focused path
    if (isGoal(this.curNode)) {
        var focusedChild = this.curNode.allChildren[this.curNode.focusIndex];
        if (
            (this.isCurNode(src) && focusedChild.id === tgt.id)
                || (src.id === focusedChild.id
                    && src.allChildren[src.focusIndex].id === tgt.id)
        ) {
            return thick;
        } else {
            return thin;
        }
    } else {
        //alert("todo");
        return thin;
    }
}

// [nodeDOM] is the DOM foreignObject, [d] is the node in the tree structure
function updateNodeMeasures(nodeDOM, d) {
    var elementToMeasure =
        isTactic(d)
        ? nodeDOM.firstChild // get the span
        : nodeDOM // get the foreignObject itself
    ;
    // we save in the rect field the size of the text rectangle
    var rect = elementToMeasure.getBoundingClientRect();
    d.width = Math.ceil(rect.width);
    d.height = Math.ceil(rect.height);
}

ProofTree.prototype.update = function(callback) {

    var self = this;

    // shorter name, expected to stay constant throughout
    var curNode = this.curNode;

    // if the viewpoint has been zoomed, cancel the zoom so that the computed
    // sizes are correct
    this.resetSVGTransform();

    var nodes = this.tree.nodes(this.rootNode);
    var links = this.tree.links(nodes);

    // we build the foreignObject first, as its dimensions will guide the others
    var textSelection = this.textLayer
        .selectAll(function() { return this.getElementsByTagName("foreignObject"); })
        .data(nodes, function(d) { return d.id || (d.id = _.uniqueId()); })
    ;

    // D3 populates the children field with undefined when no children
    // it makes my life easier to instead put an empty list there
    textSelection
        .each(function(d) {
            if (!d.hasOwnProperty("children")) { d.children = []; }
        })
    ;

    var textEnter = textSelection.enter()
        .append("foreignObject")
        .classed("monospace", true)
    // the goal nodes need to be rendered at fixed width goalNodeWidth
    // the tactic nodes will be resized to their actual width later
        .attr("width", function(d) {
            return isGoal(d) ? self.goalNodeWidth : self.tacticNodeMaxWidth;
        })
    ;

    textEnter
        .append("xhtml:body")
        //.classed("svg", true)
        .style("padding", function(d) {
            return isGoal(d) ? goalBodyPadding + "px" : "4px 0px";
        })
        .style("background-color", "rgba(0, 0, 0, 0)")
        .style("font-family", "monospace")
        .each(function(d) {
            var jqObject = $(d3.select(this).node());
            var jQContents;
            if (isTactic(d)) {
                d.span = $("<span>")
                    .addClass("tacticNode")
                    .css("padding", "4px")
                    .text(d.pName);
                jQContents = d.span;
            } else {
                jQContents = $("<div>").addClass("goalNode");
                _(d.hyps).each(function(h) {
                    var jQDiv = $("<div>")
                        .html(PT.showHypothesis(h))
                        .attr("id", _.uniqueId())
                    ;
                    h.div = jQDiv[0];
                    jQContents.append(h.div);
                });
                jQContents.append($("<hr>"));
                d.goalSpan = $("<span>").html(showTerm(d.name));
                jQContents.append(d.goalSpan);
            }
            jqObject.append(jQContents);
        })
        .each(function(d) {
            var nodeDOM = d3.select(this).node();
            updateNodeMeasures(nodeDOM, d);
        })
    ;

    textSelection
        // preset the width to update measures correctly
        .attr("width", function(d) {
            return isGoal(d) ? self.goalNodeWidth : self.tacticNodeMaxWidth;
        })
        .attr("height", "")
        .each(function(d) {
            var nodeDOM = d3.select(this).node().firstChild;
            updateNodeMeasures(nodeDOM, d);
        })
    ;

    // Now that the nodes have a size, we can compute the factors

    var curGoal = this.curGoal();
    var visibleChildren = _(this.getVisibleChildren(curGoal));
    var visibleGrandChildren = _(this.getVisibleGrandChildren(curGoal));
    var visibleNodes = _([]);
    if (hasParent(curGoal)) { visibleNodes = visibleNodes.concat([curGoal.parent]); }
    visibleNodes = visibleNodes.concat([curGoal]);
    visibleNodes = visibleNodes.concat(visibleChildren.value());
    visibleNodes = visibleNodes.concat(visibleGrandChildren.value());
    var minXNode = _(visibleNodes).min(nodeX).value();
    var maxXNode = _(visibleNodes).max(nodeX).value();
    var minX = nodeX(minXNode), maxX = nodeX(maxXNode);
    var dX = maxX - minX;

    /*
      we want: width = goalNodeWidth/2 + xFactor * dX + goalNodeWidth/2
    */
    this.xFactor = dX === 0
        ? this.width
        : (this.width - minXNode.width / 2 - maxXNode.width / 2) / dX
    ;

    /*
      we want all visible grand children to be apart from each other
      i.e. ∀ a b, yFactor * | a.y - b.y | > a.height/2 + b.height/2 + nodeVSpacing
      we also want all visible children to be apart from each other (especially when they
      don't have their own children to separate them)
    */
    var gcSiblings = _.zip(visibleGrandChildren.value(), visibleGrandChildren.rest().value());
    gcSiblings.pop(); // removes the [last, undefined] pair at the end
    var cSiblings = _.zip(visibleChildren.value(), visibleChildren.rest().value());
    cSiblings.pop();
    var siblings = _(gcSiblings.concat(cSiblings));
    var yFactors = siblings
        .map(function(e) {
            var a = e[0], b = e[1];
            return (((a.height + b.height) / 2) + nodeVSpacing) / (nodeY(b) - nodeY(a));
        })
        .value()
    ;
    this.yFactor = _.isEmpty(yFactors) ? this.height : _.max(yFactors);

    var topMostDescendant = undefined;
    // when we are focused on a tactic, it becomes the 0-th child of its current goal
    var topMostTacticIndex = isGoal(this.curNode) ? curGoal.focusIndex : 0;
    var topMostTactic = this.getVisibleChildren(curGoal)[topMostTacticIndex];
    if (topMostTactic !== undefined) {
        topMostDescendant = topMostTactic;
        var topMostGoal = this.getVisibleChildren(topMostTactic)[topMostTactic.focusIndex];
        if (topMostGoal !== undefined) {
            topMostDescendant = topMostGoal;
        }
    }
    if (topMostDescendant !== undefined) {
        if (isGoal(this.curNode) && isGoal(topMostDescendant)) {
            // computing the difference in height between the <hr> is not obvious...
            var hrDelta =
                this.curNode.goalSpan[0].offsetTop
                - topMostDescendant.goalSpan[0].offsetTop
            ;
            this.descendantsOffset =
                this.yFactor * (nodeY(curGoal) - nodeY(topMostDescendant))
                - (curGoal.height - topMostDescendant.height) / 2
                + hrDelta
            ;
        } else {
            this.descendantsOffset =
                this.yFactor * (nodeY(curGoal) - nodeY(topMostDescendant))
            ;
        }
    } else {
        this.descendantsOffset = 0;
    }

    // now we need to set the x and y attributes of the entering foreignObjects,
    // so we need to reuse the selection
    textEnter
        .attr("x", function(d) {
            if (hasParent(d)) {
                // non-roots are spawned at their parent's (cX0, cY0)
                d.cX0 = d.parent.cX0;
                d.cY0 = d.parent.cY0;
            } else {
                // the root stores its own (x0, y0)
                d.cX0 = d.x0 * self.xFactor + self.xOffset(d);
                d.cY0 = d.y0 * self.yFactor + self.yOffset(d);
            }
            return d.cX0;
        })
        .attr("y", function(d, ndx) { return d.cY0; })
    ;

    textSelection
        .each(function(d) {
            d.cX = nodeX(d) * self.xFactor + self.xOffset(d);
            d.cY = nodeY(d) * self.yFactor + self.yOffset(d);
        })
        // preset the width to update measures correctly
/*
        .attr("width", function(d) {
            return isGoal(d) ? self.goalNodeWidth : self.tacticNodeMaxWidth;
        })
        .attr("height", "")
        .each(function(d) {
            var nodeDOM = d3.select(this).node().firstChild;
            updateNodeMeasures(nodeDOM, d);
        })
*/
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .transition()
        .duration(animationDuration)
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
        .each("end", function() {
            // this is in "end" so that it does not trigger before nodes are positioned
            d3.select(this)
                .on("mouseover", function(d1) {
                    self.usingKeyboard = false;
                    self.hoveredNode = d1;
                    // update links width
                    self.linkLayer.selectAll("path").data(links, byLinkId)
                        .attr("stroke-width", self.linkWidth.bind(self))
                    ;
                    self.diffLayer.selectAll("g.diff")
                        .style("opacity", 0);
                    self.diffLayer.selectAll("g.diff")
                        .filter(function(d2) {
                            // the first condition makes sure diffs don't show up for
                            // nodes whose grandparents are off-screen
                            return self.isCurGoalGrandChild(d2) && d1.id === d2.id;
                        })
                        .style("opacity", 1);
                })
                .on("mouseout", function(d1) {
                    self.usingKeyboard = false;
                    self.hoveredNode = undefined;
                    // update links width
                    self.linkLayer.selectAll("path").data(links, byLinkId)
                        .attr("stroke-width", self.linkWidth.bind(self))
                    ;
                    self.diffLayer.selectAll("g.diff")
                        .style("opacity", 0);
                    /* actually this is annoying because diffs won't go away
                    var focusChild = getAllChildren(curNode)[curNode.focusIndex];
                    if (focusChild !== undefined) {
                        var focusGrandChild = getAllChildren(focusChild)[focusChild.focusIndex];
                        if (focusGrandChild !== undefined) {
                            self.diffLayer.selectAll("g.diff")
                                .filter(function(d) { return d.id === focusGrandChild.id; })
                                .style("opacity", 1);
                        }
                    }
                    */
                })
                .on("click", function(d) {

                    syncLogAction("CLICK " + nodeString(d));

                    self.click(d);

                })
        })
    ;

    textSelection.exit()
        .transition()
        .duration(animationDuration)
        .attr("x", function(d) {
            // in general, nodes should move towards the parent goal node
            if (!hasParent(d) || self.isRootNode(d)) {
                return d.cX;
            }
            if (isGoal(d)) {
                var nodeToReach = d.parent.parent;
                d.cX = nodeToReach.cX;
                d.cY = nodeToReach.cY;
            } else {
                var nodeToReach = d.parent;
                d.cX = nodeToReach.cX;
                d.cY = nodeToReach.cY;
            }
            return d.cX;
        })
        .attr("y", function(d) { return d.cY; })
        .style("opacity", "0")
        .remove()
    ;

    var rectSelection = this.rectLayer.selectAll("rect").data(nodes, byNodeId);

    rectSelection.enter()
        .append("rect")
        .classed("goal", isGoal)
        .classed("tactic", isTactic)
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .attr("x", function(d) { return d.cX0; })
        .attr("y", function(d) { return d.cY0; })
        .attr("rx", function(d) { return isTactic(d) ? 10 : 0; })
    ;

    rectSelection
        .classed("current", function(d) { return self.isCurNode(d); })
        .classed("solved", function(d) { return d.solved; })
        .transition()
        .duration(animationDuration)
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
    ;

    rectSelection.exit()
        .transition()
        .duration(animationDuration)
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
        .style("opacity", "0")
        .remove()
    ;

    var linkSelection = this.linkLayer.selectAll("path").data(links, byLinkId);

    linkSelection.enter()
        .append("path")
        .classed("link", true)
        .attr("d", function(d) {
            var src = swapXY(centerRight0(d.source));
            var tgt = swapXY(centerLeft0(d.target));
            return self.diagonal({"source": src, "target": tgt});
        })
    ;

    linkSelection
        .transition()
        .duration(animationDuration)
        .attr("d", function(d) {
            var src = swapXY(centerRight(d.source));
            var tgt = swapXY(centerLeft(d.target));
            return self.diagonal({"source": src, "target": tgt});
        })
        .attr("stroke-width", self.linkWidth.bind(self))
    ;

    linkSelection.exit()
        .transition()
        .duration(animationDuration)
        .attr("d", function(d) {
            var src = swapXY(centerRight(d.source));
            var tgt = swapXY(centerLeft(d.target));
            return self.diagonal({"source": src, "target": tgt});
        })
        .style("opacity", "0")
        .remove()
    ;

    this.viewportX = - (hasParent(curNode) ? curNode.parent.cX : curNode.cX);
    this.viewportY =
        - (
            (isGoal(curNode))
                ? (curNode.cY + curNode.height / 2 - this.height / 2)
                : (curNode.parent.cY + curNode.parent.height / 2 - this.height / 2)
        )
    ;
    /* was:
       - (hasParent(curGoal)
       ? Math.min(curGoal.cY, curGoal.parent.cY)
       : curGoal.cY
       );
    */

    this.viewport
        .transition()
        .duration(animationDuration)
        .attr("transform", "translate(" + self.viewportX + ", " + self.viewportY + ")")
    ;

    var diffSelection = this.diffLayer.selectAll("g.node-diff").data(
        // only goal nodes with a grandparent give rise to a diff
        _(nodes).filter(function(d) { return isGoal(d) && hasGrandParent(d); }).value(),
        byNodeId
    );

    diffSelection.enter()
        .append("g")
        .classed("node-diff", true)
        .classed("diff", true)
        .each(function(d) {
            var gp = d.parent.parent;

            var d3this = d3.select(this);

            // adding diffs for the goal

            var subdiff = spotTheDifferences(gp.goalSpan, d.goalSpan);

            d.removedSelection =
                d3this.selectAll("rect.removed").data(subdiff.removed);

            d.removedSelection.enter()
                .append("rect")
                .classed("removed", true)
                .attr("fill", diffRed)
            ;

            d.addedSelection =
                d3this.selectAll("rect.added").data(subdiff.added);

            d.addedSelection.enter()
                .append("rect")
                .classed("added", true)
                .attr("fill", diffGreen)
            ;

            // adding diffs for the hypotheses

            var oldHyps = gp.hyps.slice(); // slice() creates a shallow copy
            var newHyps = d.hyps.slice();

            var diff = computeDiff(oldHyps, newHyps);
            var removed = diff.removed;
            var changed = diff.changed;
            var added   = diff.added;

            var diffList = [];
            // try to match old and new hypotheses that are the same
            while (oldHyps.length !== 0 && newHyps.length !== 0) {
                var oldChanged = _(changed).some(function(c) {
                    return c.before.hName === oldHyps[0].hName;
                });
                var newChanged = _(changed).some(function(c) {
                    return c.after.hName === newHyps[0].hName;
                });
                if (oldChanged && newChanged) {
                    var oldHyp = oldHyps.shift(), newHyp = newHyps.shift();
                    diffList.push({ "oldHyp": oldHyp, "newHyp": newHyp });
                } else if (oldChanged) {
                    var newHyp = newHyps.shift();
                    diffList.push({ "oldHyp": undefined, "newHyp": newHyp });
                } else if (newChanged) {
                    var oldHyp = oldHyps.shift();
                    diffList.push({ "oldHyp": oldHyp, "newHyp": undefined });
                } else {
                    var oldHyp = oldHyps.shift();
                    diffList.push({ "oldHyp": oldHyp, "newHyp": undefined });
                }
            }
            // just push the remainder
            _(oldHyps).each(function(oldHyp) {
                diffList.push({ "oldHyp": oldHyp, "newHyp": undefined });
            });
            _(newHyps).each(function(newHyp) {
                    diffList.push({ "oldHyp": undefined, "newHyp": newHyp });
            });

            d.diffListSelection =
                d3.select(this).selectAll("g.diff-item").data(diffList, byDiffId);

            d.diffListSelection.enter()
                .append("g")
                .classed("diff-item", true)
                .attr("id", byDiffId)
                .each(function(diff) {

                    var d3this = d3.select(this);

                    if (diff.oldHyp === undefined) {

                        var newHyp = diff.newHyp;
                        d3this
                            .append("path")
                            .attr("fill", diffGreen)
                            .attr("opacity", diffOpacity)
                            .attr("stroke", "black")
                            .attr("stroke-width", 0)
                        ;

                    } else if (diff.newHyp === undefined) {

                        var oldHyp = diff.oldHyp;
                        d3this
                            .append("path")
                            .attr("fill", diffRed)
                            .attr("stroke", redStroke)
                            .attr("opacity", diffOpacity)
                        ;

                    } else {

                        var oldHyp = diff.oldHyp;
                        var newHyp = diff.newHyp;
                        if (JSON.stringify(oldHyp.hType) !== JSON.stringify(newHyp.hType)) {
                            d3this
                                .append("path")
                                .attr("fill", diffBlue)
                                .attr("stroke", blueStroke)
                                .attr("opacity", diffOpacity)
                            ;

                            var subdiff = spotTheDifferences(oldHyp.div, newHyp.div);

                            diff.removedSelection =
                                d3this.selectAll("rect.removed").data(subdiff.removed);

                            diff.removedSelection.enter()
                                .append("rect")
                                .classed("removed", true)
                                .attr("fill", diffRed)
                            ;

                            diff.addedSelection =
                                d3this.selectAll("rect.added").data(subdiff.added);

                            diff.addedSelection.enter()
                                .append("rect")
                                .classed("added", true)
                                .attr("fill", diffGreen)
                            ;

                        }

                    }
                })
            ;

        })
    ;

    diffSelection
        .each(function(d) {
            var gp = d.parent.parent;

            // updating the goal diffs

            d.removedSelection
                .each(function(jSpan) {
                    var rect = elmtRect(gp, jSpan[0]);
                    d3.select(this)
                        .transition()
                        .duration(animationDuration)
                        .attr("x", rect.left)
                        .attr("y", rect.top)
                        .attr("width", rect.width)
                        .attr("height", rect.height)
                    ;
                })
            ;

            d.addedSelection
                .each(function(jSpan) {
                    var rect = elmtRect(d, jSpan[0]);
                    d3.select(this)
                        .transition()
                        .duration(animationDuration)
                        .attr("x", rect.left)
                        .attr("y", rect.top)
                        .attr("width", rect.width)
                        .attr("height", rect.height)
                    ;
                })
            ;

            // updating the hypotheses diffs

            // keep track of how far we are vertically to draw the diffs with
            // only one side nicely
            var leftY = gp.cY + goalBodyPadding;
            var rightY = d.cY + goalBodyPadding;

            d.diffListSelection
                .each(function(diff) {

                    if (diff.oldHyp === undefined) {

                        var newHyp = diff.newHyp;
                        d3.select(this).select("path")
                            .transition()
                            .duration(animationDuration)
                            .attr(
                                "d",
                                connectRects(
                                    emptyRect(gp, leftY),
                                    elmtRect(d, newHyp.div),
                                    d.parent.cX
                                )
                            )
                        ;
                        rightY = elmtRect(d, newHyp.div).bottom;

                    } else if (diff.newHyp === undefined) {

                        var oldHyp = diff.oldHyp;
                        d3.select(this).select("path")
                            .transition()
                            .duration(animationDuration)
                            .attr(
                                "d",
                                connectRects(
                                    elmtRect(gp, oldHyp.div),
                                    emptyRect(d, rightY),
                                    d.parent.cX
                                )
                            )
                        ;
                        leftY = elmtRect(gp, oldHyp.div).bottom;

                    } else {

                        var oldHyp = diff.oldHyp;
                        var newHyp = diff.newHyp;
                        if (JSON.stringify(oldHyp.hType) !== JSON.stringify(newHyp.hType)) {
                            d3.select(this).select("path")
                                .transition()
                                .duration(animationDuration)
                                .attr(
                                    "d",
                                    connectRects(
                                        elmtRect(gp, oldHyp.div),
                                        elmtRect(d, newHyp.div),
                                        d.parent.cX
                                    )
                                )
                            ;
                        }
                        leftY = elmtRect(gp, oldHyp.div).bottom;
                        rightY = elmtRect(d, newHyp.div).bottom;

                    }

                    if (diff.hasOwnProperty("removedSelection")) {
                        diff.removedSelection
                            .each(function(jSpan) {
                                var rect = elmtRect(gp, jSpan[0]);
                                d3.select(this)
                                    .transition()
                                    .duration(animationDuration)
                                    .attr("x", rect.left)
                                    .attr("y", rect.top)
                                    .attr("width", rect.width)
                                    .attr("height", rect.height)
                                ;
                            })
                        ;
                    }

                    if (diff.hasOwnProperty("addedSelection")) {
                        diff.addedSelection
                            .each(function(jSpan) {
                                var rect = elmtRect(d, jSpan[0]);
                                d3.select(this)
                                    .transition()
                                    .duration(animationDuration)
                                    .attr("x", rect.left)
                                    .attr("y", rect.top)
                                    .attr("width", rect.width)
                                    .attr("height", rect.height)
                                ;
                            })
                        ;
                    }

                })
            ;

        })
        .style("opacity", 0)
        .transition()
        .duration(animationDuration)
        .style("opacity", function(d) {
            if (!self.isCurNodeGrandChild(d)) { return 0; }
            var gp = d.parent.parent;
            var focusChild = gp.allChildren[gp.focusIndex];
            var focusGrandChild = focusChild.allChildren[focusChild.focusIndex];
            return (focusGrandChild !== undefined && d.id === focusGrandChild.id) ? 1 : 0;
        })
    ;

    diffSelection.exit()
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

    this.updateDebug();

    this.animationRunning = true;
    window.setTimeout(function() {
        self.animationRunning = false;
        if (callback !== undefined) {
            callback();
        }
        self.afterUpdate(self);
    }, animationDuration);

}

function byDiffId(d) {
    var res = "{";
    if (d.oldHyp !== undefined) { res += $(d.oldHyp.div).attr("id"); }
    res += "-";
    if (d.newHyp !== undefined) { res += $(d.newHyp.div).attr("id"); }
    return res + "}";
}

function computeDiff(oldHyps, newHyps) {

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

    return {
        "removed": removed,
        "changed": changed,
        "added":   added,
    };

}

function elmtRect(node, elmt) {
    var rect = elmt.getBoundingClientRect();
    var containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect();
    var left = node.cX + deltaX(containerRect, rect);
    var top = node.cY + deltaY(containerRect, rect);
    return {
        "left": left, "right": left + rect.width, "width": rect.width,
        "top": top, "bottom": top + rect.height, "height": rect.height,
    };
}

ProofTree.prototype.shiftPrev = function(n) {
    if (this.paused) { return; }
    var self = this;
    function tryShifting(n) {
        if (n.focusIndex> 0) {
            n.focusIndex--;
            syncLogAction("UP " + nodeString(n.allChildren[n.focusIndex]));
            self.update();
            return true;
        }
        return false;
    }
    if (n.solved) { return; }
    if (isGoal(n)) {
        tryShifting(n.children[n.focusIndex])
            || tryShifting(n);
    } else {
        tryShifting(n);
    }
}

ProofTree.prototype.shiftNext = function(n) {
    if (this.paused) { return; }
    var self = this;
    function tryShifting(n) {
        if (n.focusIndex + 1 < self.getVisibleChildren(n).length) {
            n.focusIndex++;
            syncLogAction("DOWN " + nodeString(n.allChildren[n.focusIndex]));
            self.update();
            return true;
        }
        return false;
    }
    if (n.solved) { return; }
    if (isGoal(n)) {
        tryShifting(n.children[n.focusIndex])
            || tryShifting(n);
    } else {
        tryShifting(n);
    }
}

ProofTree.prototype.click = function(d, remember, callback) {

    if (this.animationRunning || this.paused) { return; }

    if (d.solved) {
        if (hasParent(d)) {
            this.click(d.parent, remember, callback);
        }
        return;
    }

    // when the user clicks on a tactic node below
    // bring them to the first unsolved goal instead
    if (isTactic(d) && d.depth > this.curNode.depth && d.allChildren.length > 0) {
        expand(d);
        var firstUnsolved = _(d.allChildren)
            .find(function(e) { return !e.solved; });
        if (firstUnsolved !== undefined) {
            this.click(firstUnsolved, remember, callback);
            return;
        }
    }

    // when the user clicks on the parent tactic, bring them back to its parent
    if (isTactic(d) && d.depth < this.curNode.depth) {
        this.click(d.parent, remember, callback);
        return;
    }

    this.navigateTo(d, remember);

    if (_.isEmpty(d.allChildren)) {
        if (isGoal(d)) {
            d.allChildren = this.tryAllTactics();
        }
        // otherwise, this is a terminating tactic for this goal!
        else {
            this.solved(d);
        }
    }

    expand(d);
    this.update(callback);

}

// called when n has been solved
ProofTree.prototype.solved = function(n) {
    var self = this;
    n.solved = true;
    collapse(n);
    if (hasParent(n)) {
        this.navigateTo(n.parent);
        this.animationRunning = true;
        window.setTimeout(function () {
            self.childSolved(n.parent);
            self.update();
            self.animationRunning = false;
        }, animationDuration);
    } else {
        window.setTimeout(function () {
            syncLogAction("QED " + JSON.stringify(PT.proofFrom(self.rootNode)));
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

function collapse(d) { d.collapsed = true; }

function collapseChildren(d) { _(d.allChildren).forEach(collapse); }

function expand(d) {
    d.collapsed = false;
    if (isGoal(d)) {
        _(d.allChildren).each(expand);
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

/*
We need to compute how many layers of focusing are solved by a terminating
tactic because of the way Undo works.
Since we Undo every proved branch before navigating to another branch, this
depth is always how deep the node is to its first ancestor with more than
one child (since the other child will then remain to be proved).
*/
function depthSolved(tacNode) {
    if (_(tacNode.children).size() <= 1) {
        if (!hasGrandParent(tacNode)) { return 1; }
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
                    if (src.terminating) {
                        _(_.range(depthSolved(src))).each(function() {
                            syncQuery('Undo.', hIgnore);
                        });
                    }
                    syncQuery('Undo.', hIgnore);
                } else {
                    // 'Back.' does not work in -ideslave
                    // 'Back.' takes one step to undo 'Show.'
                    // 'Undo.' works in -ideslave
                    // 'Undo.' does not care about 'Show.' commands
                    // Undo the 'Focus.' command.
                    // Do not use 'Unfocus.' as it is itself undone by 'Undo.'
                    syncQuery('Undo.', hIgnore);
                }

            } else { // going down

                // hide sibling tactic nodes
                if (isGoal(src)) {
                    collapse(src);
                }

                if (isTactic(dst)) {
                    syncQuery(dst.name, hIgnore);
                } else {
                    syncQuery('Focus ' + dst.ndx + '.', hIgnore);
                }

            }
        })
    ;

    this.curNode = dest;

}

function isTactic(n) { return (n.depth % 2 === 1); }

function isGoal(n) { return (n.depth % 2 === 0); }

function hIgnore(response) { }

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

function keydownDispatcher() {
    if (activeProofTree !== undefined) {
        activeProofTree.keydownHandler.call(activeProofTree);
    }
}

ProofTree.prototype.keydownHandler = function() {

    // don't interact while typing
    if (d3.event.target.type === "textarea") { return; }

    var curNode = this.curNode;

    var children = this.getVisibleChildren(curNode);

    if (this.animationRunning) {
        // all keys are frozen during animation
        d3.event.preventDefault();
        return;
    }

    this.usingKeyboard = true;

    switch (d3.event.keyCode) {

    case 37: // Left
    case 65: // a
        if (hasParent(curNode)) {
            syncLogAction("LEFT " + nodeString(curNode.parent));
            this.click(curNode.parent);
        }
        break;

    case 39: // Right
    case 68: // d
        var dest = children[curNode.focusIndex];
        syncLogAction("RIGHT " + nodeString(dest));
        this.click(dest);
        break;

    case 38: // Up
    case 87: // w
        this.shiftPrev(curNode);
        break;

    case 40: // Down
    case 83: // s
        this.shiftNext(curNode);
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

    default:
        //console.log("Unhandled event", d3.event.keyCode);
        return;
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
                .css("background-color", "#CB99C9")
                .css("resize", "none")
            ;
            PT.resizeTextarea.call(ta);
            result.append(ta);
            result.append(
                $("<button>")
                    .css("margin", 0)
                    .css("padding", "0px 2px")
                    .css("border", 0)
                    .css("background-color", "#BB89B9")
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
                        self.update(function() {
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

PT.pprintAux = function(proof, indentation, whiteSpace, lineSep) {

    if (_.isEmpty(proof)) { return ""; }

    var fst = proof[0];
    var snd = proof[1];
    var indent = repeat(2 * indentation, whiteSpace);

    //if (fst === "todo.") { fst = '<span style="color: green;">admit.</span>'; }

    if (_.isEmpty(snd)) { return fst; }

    if (_(snd).size() === 1) {
        return fst + " "
            + _(snd).reduce(
                function(acc, elt) {
                    return acc + PT.pprintAux(elt, indentation, whiteSpace, lineSep);
                },
                ""
            )
        ;
    }

    return fst
        + _(snd).reduce(
            function(acc, elt) {
                return acc
                    + lineSep + indent
                    + "{ " + PT.pprintAux(elt, indentation + 1, whiteSpace, lineSep)
                    + (hasBranching(elt) ? lineSep + indent + "}" : " }")
                ;
            },
            ""
        )
    ;

}

PT.pprint = function(proof, indentation, whiteSpace, lineSep) {
    if (indentation === undefined) { indentation = 0; }
    if (whiteSpace === undefined) { whiteSpace = nbsp; }
    if (lineSep === undefined) { lineSep = "\n"; }
    return repeat(2 * indentation, whiteSpace)
        + PT.pprintAux(proof, indentation, whiteSpace, lineSep);
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
        syncQuery(fst, function(response) {
            if (isGood(response)) {
                var needToFocus = snd.length > 1;
                _(snd).each(function(n) {
                    if (needToFocus) { syncQuery(" { ", function(){}); }
                    self.replayThisProof(n);
                    if (needToFocus) { syncQuery(" } ", function(){}); }
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
    syncQuery("Qed.", function(response) {
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
    if (t[1] === null) {
        return showNames(t[0]);
    } else {
        return showNames(t[0]) + syntax(":") + nbsp + showTermAux(t[1], 0, 0, false);
    }
}

function showPatternAux(p, withParens) {
    switch (p.tag) {
        case "Wildcard":
        return "_";
        break;

        case "Pattern":
        var c = p.contents;
        if (c[1].length === 0) { // constructor with no parameters, never parenthesized
            return c[0];
        } else { // constructor with parameters, parenthesized if subpattern
            if (c[0] === "cons" && c[1].length === 2) {
                return (withParens ? syntax("(") : "")
                    + showPatternAux(c[1][0], true)
                    + nbsp + syntax("::") + nbsp
                    + showPattern(c[1][1], false)
                    + (withParens ? syntax(")") : "")
                ;
            } else {
                return (withParens ? syntax("(") : "")
                    + _(c[1]).reduce(function(acc, elt) {
                        return acc + " " + showPatternAux(elt, true);
                    }, c[0])
                    + (withParens ? syntax(")") : "")
                ;
            }
        }
    };
}

function showPattern(p) { return showPatternAux(p, false); }

function showPatterns(ps) {
    if (ps.length === 1) {
        var patterns = ps[0];
        return _(patterns).rest().reduce(function(acc, pattern) {
            return acc + syntax(", ") + showPattern(pattern);
        }, showPattern(patterns[0]));
    } else {
        alert("TODO");
    }
}

function showNames(t) {
    if (_.isEmpty(t)) { return ""; }
    return ident(t[0]) + " " + showNames(_(t).rest().value());
}

function showTerm(t) {
    return showTermAux(t, 0, 0, true);
}

function showTermIndent(t, indent) {
    return showTermAux(t, indent, 0, true);
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
var precAppend = precedence++;
var precCons   = precedence++;
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

    case "Definition":
        var name = c[0];
        var args = _(c[1]).map(showBinder);
        var type = (c[2] !== null)
            ? syntax(":") + nbsp + showTermInline(c[2]) + nbsp
            : "";
        var term = showTermIndent(c[3], 1);
        return vernac("Definition")
            + nbsp
            + ident(name)
            + nbsp
            + _(args).reduce(function(acc, elt) {
                return acc + syntax("(") + elt + syntax(")") + nbsp; }, "")
            + type
            + syntax(":=")
            + "<br>" + getIndent(1)
            + term
            + syntax(".")
        ;

    case "Fixpoint":
        var name = c[0];
        var args = _(c[1]).map(showBinder);
        var decreasing = c[2];
        var type = (c[3] !== null)
            ? syntax(":") + nbsp + showTermInline(c[3]) + nbsp
            : "";
        var term = showTermIndent(c[4], 1);
        return vernac("Fixpoint")
            + nbsp
            + ident(name)
            + nbsp
            + _(args).reduce(function(acc, elt) {
                return acc + syntax("(") + elt + syntax(")") + nbsp; }, "")
            + (
                (decreasing !== null)
                    ? syntax("{") + nbsp + syntax("struct")
                    + nbsp + decreasing + nbsp + syntax("}") + nbsp
                    : ""
            )
            + type
            + syntax(":=")
            + "<br>" + getIndent(1)
            + term
            + syntax(".")
        ;

    default:
        return "Unknown Vernacular tag: " + t.tag;

    };
}

function showTermText(t) {
    return $(showTermInline(t)).text();
}

function showMatchItems(items) {
    return _(items).rest().reduce(function(acc, term) {
        return acc + syntax(", ") + showTermInline(term);
    }, showTermInline(items[0]));
}

/*
  [t]           the term to show
  [indentation] the indentation to use if you make a newline
  [precParent]  the precedence of the parent operator (for parenthesizing)
  [newline]     true if the term should feel free to use multiple lines
*/
function showTermAux(t, indentation, precParent, newline) {
    var c = t.contents;

    var indent = getIndent(indentation);

    var par = function(precOp, text) {
        if (precOp <= precParent) {
            return term(syntax("(") + text + syntax(")"));
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

    case "Match":
        var matchItems = c[0];
        var equations = c[1];
        return term(
            syntax("match") + nbsp
                + showMatchItems(matchItems) + nbsp
                + syntax("with") + "<br>"
                + _(equations).reduce(function(acc, elt) {
                    var patterns = showPatterns(elt[0]);
                    var body = showTermAux(elt[1], indentation + 1, precParent, newline);
                    return acc
                        + getIndent(indentation) + syntax("|") + nbsp
                        + patterns
                        + nbsp
                        + syntax("=>")
                        + (
                            (body.indexOf("<br>") === -1)
                                ? nbsp + body
                                : "<br>" + getIndent(indentation + 1) + body
                        )
                        + "<br>";
                }, "")
            //showTermAux(c[0], indentation, precArrow, false)
            + getIndent(indentation) + syntax("end")
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

            case "cons":
                return showOp(c, "::", precCons);

            case "app":
                return showOp(c, "++", precAppend);

            default:
                // nothing, fall through

            };
        }

        return par(
            precApp,
            showTermAux(c[0], 0, precApp - 1, false) + " "
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

function nodeString(d) {
    return JSON.stringify(
        {
            "id": d.id,
            "depth": d.depth,
            "pName": d.pName,
            "hyps": _(d.hyps).map(function(h) { return {
                "hName": h.hName,
                "hType": h.hType,
                "hValue": h.hValue,
            }; }).value(),
            "name": d.name,
        }
    );
}

ProofTree.prototype.updateDebug = function() {

    this.debug
        .selectAll(function() { return this.getElementsByTagName("foreignObject"); })
        .attr("width", this.width)
    ;
    this.debug.select("rect").attr("width", this.width);

    var debugDiv = this.debug.select('div');
    var jDebugDiv = $(debugDiv[0]);

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
