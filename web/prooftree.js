"use strict";

/*
  Note: in strict mode, eval does not populate the global namespace with global
  scope variables. Therefore $.getScript will not see the global variables
  unless they are attached to window manually. Since I like strict mode, things
  to be exported have to be registered in the PT namespace.
*/
window.PT = {};

// CONFIGURATION
var svgPanEnabled = true;
var nodeVSpacing = 10;
var nodeStroke = 2;
var rectMargin = {top: 2, right: 8, bottom: 2, left: 8};
var animationDuration = 300;
var tacticNodeRounding = 10;
var goalNodeRounding = 0;
var keyboardDelay = 100;
var keyboardPaused = false;

$(document).ready(function() {

    /* DISABLED for lecture.js, this should be opt-in

    $(window).click(function(event) {
        // TODO: this is kinda clunky, but at least we can mark tutorial windows
        // as non-disactivating
        // if the click did not originate in a SVG, disactivate proof trees
        if ($(event.target).closest(".svg").length === 0) {
            activeProofTree = undefined;
        }
    });
    */

    setupTextareaResizing();
});

var diffRed   = "#EE8888";
var diffGreen = "#88EE88";
var diffBlue  = "#8888EE";
var diffOpacity = 0.8;
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
function ProofTree(anchor, width, height, qedCallback,
                   onStartProcessing, onEndProcessing) {

    var self = this;

    this.anchor = d3.select(anchor);
    this.width = width;
    this.height = height;
    this.qedCallback = qedCallback;
    this.onStartProcessing = onStartProcessing;
    this.onEndProcessing = onEndProcessing;

    this.paused = false;
    this.svgId = _.uniqueId();
    this.xFactor = this.width;
    this.yFactor = this.height;
    this.userState = {};
    this.usingKeyboard = false;
    this.goalWidth = computeGoalWidth(this.width);
    this.tacticWidth = computeTacticWidth(this.width);

    this.tree = d3.layout.tree()
        .children(self.getViewChildren.bind(self))
        .separation(function(d) {
            // TODO: this just won't work, need invisible children
            // for tactics without children
            return 1 / (1 + (d.depth * d.depth * d.depth));
        })
    ;

    this.diagonal = d3.svg
        .diagonal()
        .projection(function(d) { return [d.y, d.x]; })
    ;

    d3.select("body")
        .on("keydown", function() {
            // capture events only if we are in proof mode
            if ($("#prooftree").css("display") !== "none") {
                self.keydownHandler();
            }
        })
    ;

    this.div = this.anchor
        .insert("div", ":first-child")
        .attr("id", "pt-" + this.svgId)
        .classed("prooftree", true)
    ;

    this.svg = this.div
        .insert("svg", ":first-child")
        .classed("svg", true)
        .attr("id", "svg-" + this.svgId)
    // necessary for the height to be exactly what we set
        .attr("display", "block")
        .style("width", this.width + "px")
        .style("height", this.height + "px")
        //.attr("focusable", true)
    // this creates a blue outline that changes the width weirdly
        //.attr("tabindex", 0)
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
              "translate(" + self.goalWidth + ", " + 0 + ")"
             )
    ;

    // Note : the order of these influence the display:
    // first = bottom, last = top
    this.linkLayer = this.viewport.append("g").attr("id", "link-layer");
    this.rectLayer = this.viewport.append("g").attr("id", "rect-layer");
    this.diffLayer = this.viewport.append("g").attr("id", "diff-layer");
    this.textLayer = this.viewport.append("g").attr("id", "text-layer");
    this.tipsLayer = this.viewport.append("g").attr("id", "tips-layer");

    this.debug = this.svg.append("g");

    var debugWidth = this.width / 2;
    var debugHeight;

    var fo = this.debug
        .append("foreignObject")
        .attr("width", debugWidth + "px")
    ;

    fo
        .append("xhtml:body")
        .classed("svg", true)
        .style("background-color", "rgba(0, 0, 0, 0)")
        .style("font-family", "monospace")
        .html('<div class="node" style="overflow: auto;">'
              + '<p>No debug information</p></div>'
             )
        .each(function() {
            debugHeight = this.firstChild.getBoundingClientRect().height;
        })
    ;

    fo.attr("height", debugHeight + "px");

    this.debug
        .insert("rect", ":first-child")
        .attr("width", debugWidth  + "px")
        .attr("height", debugHeight + "px")
        .attr("fill", "#B2DBA1")
        .attr("opacity", "0.9")
    ;

    if (svgPanEnabled) {
        this.svg
            .insert("script", ":first-child")
            .attr("xlink:href", "SVGPan.js")
        ;
    }

    activeProofTree = this;

}

var goalShare = 15 / 20;
var tacticShare = 4 / 20;

function computeGoalWidth(width) {
    return Math.floor(width * (goalShare / 2));
}

function computeTacticWidth(width) {
    return Math.floor(width * (tacticShare / 2));
}

ProofTree.prototype.resize = function(width, height) {
    this.width = width;
    this.height = height;
    this.div.style("width", this.width + "px");
    this.div.style("height", this.height + "px");
    this.svg.style("width", this.width + "px");
    this.svg.style("height", this.height + "px");
    this.goalWidth = computeGoalWidth(this.width);
    this.tacticWidth = computeTacticWidth(this.width);
    this.update();
}

ProofTree.prototype.nodeWidth = function(d) {
    if (isGoal(d)) { return this.goalWidth; }
    if (isTacticish(d)) { return this.tacticWidth; }
    throw d;
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

/*

  a_____b     c_____d
  |     |     |     |
  h_____g     f_____e

*/
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

    //console.log("M", a, b, c, d, e, f, g, h);

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

/*
  creates an empty rectangle in the same column as [node], at vertical position
  [currentY]
*/
function emptyRect(node, currentY) {
    var delta = 1; // how big to make the empty rectangle
    return $.extend(
        {
            "left": node.cX,
            "right": node.cX + node.width,
            "width": node.width
        },
        {
            "top": currentY - delta,
            "bottom": currentY + delta,
            "height": 2 * delta,
        }
    );
}

function byNodeId(d) { return d.id; }
function byLinkId(d) { return d.source.id + "," + d.target.id; }

// transposition accessors
function nodeX(d) { return d.y; }
function nodeY(d) { return d.x; }

ProofTree.prototype.isFocusedChild = function(d) {
    var focusedChild = this.getFocusedChild(this.curNode);
    return (focusedChild !== undefined && d.id === focusedChild.id);
}

ProofTree.prototype.xOffset = function(d) {
    return - this.nodeWidth(d) / 2; // position the center
}

ProofTree.prototype.yOffset = function(d) {
    var offset = - d.height / 2; // for the center
    // for the focused tactic of the current goal, show it in front of its goal
    var focusedChild = this.getFocusedChild(this.curNode);
    if (
        (isGoal(this.curNode) && focusedChild !== undefined && d.id === focusedChild.id)
            ||
            (isTacticish(d) && this.isCurNode(d))
       ) {
        // return something such that cY === nodeY(d.parent) * yFactor + offset
        return offset + (nodeY(d.parent) - nodeY(d)) * this.yFactor;
    } else if (this.isCurGoalChild(d) || this.isCurGoalGrandChild(d)) {
        return offset + this.descendantsOffset;
    } else {
        return offset;
    }
}

var centerLeftOffset  = +10;

var centerRightOffset = -10;

function centerLeft0(d) {
    return {
        "x": d.cX0 + centerLeftOffset,
        "y": d.cY0 + d.height / 2
    };
}

function centerRight0(d) {
    return {
        "x": d.cX0 + d.width + centerRightOffset,
        "y": d.cY0 + d.height / 2
    };
}

function centerLeft(d) {
    return {
        "x": d.cX + centerLeftOffset,
        "y": d.cY + d.height / 2
    };
}

function centerRight(d) {
    return {
        "x": d.cX + d.width + centerRightOffset,
        "y": d.cY + d.height / 2
    };
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

/*
  [theorem] : string
  [tactics] : ProofTree -> [string]
*/
ProofTree.prototype.newTheorem = function(theorem, tactics) {

    var self = this;

    this.theorem = theorem;
    this.tactics = tactics;

    // hide previous proof result if any, show svg if hidden
    this.svg.style("display", "");

    // will be reset in hInit callback, prevents stale uses
    this.rootNode = undefined;

    var success = false;

    asyncLog("THEOREM " + theorem);

    asyncQuery(theorem)
        .then(function(response) {
            success = self.hInit(response);
            $(this.svg[0]).focus();
            this.svg.on("click")();
        })
        .catch(outputError);

}

ProofTree.prototype.newAlreadyStartedTheorem =
    function(theoremStatement, lastResponse, tactics)
{

    var self = this;

    this.theorem = theoremStatement;
    this.tactics = tactics;

    // hide previous proof result if any, show svg if hidden
    this.svg.style("display", "");

    // will be reset in hInit callback, prevents stale uses
    this.rootNode = undefined;

    var success = false;

    self.hInit(lastResponse);

    $(this.svg[0]).focus();
    this.svg.on("click")();

}

function mkNode(parent, moreFields) {
    return $.extend(
        {
            "id": _.uniqueId(),
            /*
              we preemptively fill the parent and depth fields because d3 will
              only fill them for the visible nodes of the tree, while some
              algorithms require it before a node has ever been visible
            */
            "parent": parent,
            "depth": (parent === undefined) ? 0 : parent.depth + 1,
            "solved": false,
            //nodes need to be created uncollapsed so that D3 registers them
            "collapsed": false,
        },
        moreFields
    );
}

function mkGoalNode(parent, g, ndx) {
    var goalTerm = extractGoal(g.gGoal);
    return mkNode(
        parent,
        {
            "type": "goal",
            "hyps": _(g.gHyps).map(extractHypothesis).value(),
            // this index is used to call Focus, Coq using 1-indexing
            "ndx": ndx + 1,
            "gid": g.gId,
            "goalTerm": goalTerm,
            "goalString": showTermText(goalTerm),
            "userTactics": [],
            "otherTactics": [],
            "tacticGroups": [],
            "tacticIndex": 0,
        }
    );
}

function updateGoalNode(node, newGoal) {
    var goalTerm = extractGoal(newGoal.gGoal);
    node.hyps = _(newGoal.gHyps).map(extractHypothesis).value();
    node.gid = newGoal.gId;
    node.goalTerm = goalTerm;
    node.goalString = showTermText(goalTerm);
    node.userTactics = [];
    node.otherTactics = [];
    node.tacticGroups = [];
    node.tacticIndex = 0;
}

function mkTacticNode(parent, tactic, goals) {
    // need the node to exist to populate the parent field of children
    var node = mkNode(
        parent,
        {
            "type": "tactic",
            "tactic": tactic,
            "goalIndex": 0,
        }
    );
    var goalNodes = _(goals)
        .map(_.partial(mkGoalNode, node))
        .value()
    ;
    return $.extend(node, {
        "goals": goalNodes,
        "originalGoals": goals, // saved for restoration
    });
}

/*
 * A tactics node can contain any number (even zero) tactics.
 */
function mkTacticGroupNode(parent, name) {
    return mkNode(
        parent,
        {
            "name": name,
            "type": "tacticgroup",
            "tactics": [],
            "tacticIndex": 0,
        }
    );
}

function isSolved(node) {
    if (node === undefined) {
        throw node;
    }
    return node.solved;
}

function isCollapsed(node) {
    return node.collapsed;
}

/*
  Assumes d is a non-empty tactic group
 */
function getTacticFromGroup(d) {
    return d.tactics[d.tacticIndex];
}

function getTacticFromTacticish(d) {
    if (isTactic(d)) {
        return d;
    } else if (isTacticGroup(d)) {
        return getTacticFromGroup(d);
    } else {
        throw d;
    }
}

ProofTree.prototype.getViewChildren = function(node) {
    if (isSolved(node)) { return []; }
    /*
      a node can be collapsed but an ancestor of the current node, in which case
      it has exactly one viewChild, its focused child. otherwise, D3 does not
      even reach the current node!
     */
    if (isCollapsed(node)) {
        // no need to have a child for non-ancestors of the current node
        if (!this.isCurNodeAncestor(node)) { return []; }
        // ancestors of the current node need to have a child for the current
        // node to be reachable by D3
        // the simplest way is to uncollapse, get all the children, and filter
        node.collapsed = false;
        var viewChildren = this.getViewChildren(node);
        node.collapsed = true;
        if (viewChildren.length === 0) { return []; }
        if (isGoal(node)) { return [viewChildren[node.tacticIndex]]; }
        else if (isTactic(node)) { return [viewChildren[node.goalIndex]]; }
        else if (isTacticGroup(node)) {
            var tacticSelected = getTacticFromGroup(node);
            return [viewChildren[tacticSelected.goalIndex]];
        } else {
            throw node;
        }
    }
    if (isGoal(node)) {
        var nonEmptyTacticGroups =
            _(node.tacticGroups).filter(function(group) {
                return (group.tactics.length > 0);
            }).value()
        ;
        return (
            node.userTactics
                .concat(node.otherTactics)
                .concat(nonEmptyTacticGroups)
        );
    } else if (isTacticGroup(node)) {
        // assuming node.tactics.length > 0
        // here we return the children of the focused tactic node
        return this.getViewChildren(node.tactics[node.tacticIndex]);
    } else if (isTactic(node)) {
        return node.goals;
    } else {
        throw node;
    }
}

ProofTree.prototype.getViewGrandChildren = function(node) {
    return (
        _(this.getViewChildren(node))
            .map(this.getViewChildren.bind(this))
            .flatten(true).value()
    );
}

function makeFocused(node) {
    if (isGoal(node)) {
        if (!hasParent(node)) { return; }
        node.parent.goalIndex =
            _(node.parent.goals)
            .findIndex(function(e) { return e.id === node.id; })
        ;
        if(isTacticGroup(node.parent.parent)) {
            makeFocused(node.parent.parent);
        }
    } else if (isTacticGroup(node)) {
        var indexWithinGroups = _(node.parent.tacticGroups)
            .filter(function(g) { return (g.tactics.length > 0); })
            .findIndex(function(e) { return e.id === node.id; })
        ;
        node.parent.tacticIndex = node.parent.userTactics.length
            + node.parent.otherTactics.length
            + indexWithinGroups
        ;
    } else if (isTactic(node)) {
        if (isGoal(node.parent)) {
            node.parent.tacticIndex = _(getAllTactics(node.parent))
                .findIndex(function(e) { return e.id === node.id; })
            ;
        } else if (isTacticGroup(node.parent)) {
            node.parent.tacticIndex = _(node.parent.tactics)
                .findIndex(function(e) { return e.id === node.id; })
            ;
        } else {
            throw node;
        }
    } else {
        throw node;
    }
}

/*
 * makes sure node is focused for its parent, and the same for its parent w.r.t.
 * its grandparent, so that getViewChildren returns the correct nodes
 */
function makeFocusedTwoGenerations(node) {
    makeFocused(node);
    if (hasParent(node)) {
        if (isGoal(node) && isTacticGroup(node.parent.parent)) {
            makeFocused(node.parent.parent);
        } else {
            makeFocused(node.parent);
        }
    }
}

ProofTree.prototype.getFocusedChild = function(node) {

    if (node === undefined) {
        console.log('break');
    }

    var viewChildren = this.getViewChildren(node);
    if (viewChildren.length === 0) {
        return undefined;
    }
    if (isGoal(node)) {
        return viewChildren[node.tacticIndex];
    } else if (isTactic(node)) {
        return viewChildren[node.goalIndex];
    } else if (isTacticGroup(node)) {
        return viewChildren[node.tactics[node.tacticIndex].goalIndex];
    }
}

function getAllTactics(node) {
    if (isGoal(node)) {
        var tacticsFromGroups =
            _(node.tacticGroups)
            .map(function(group) { return group.tactics; })
            .flatten(true)
            .value()
        ;
        return node.userTactics
            .concat(node.otherTactics)
            .concat(tacticsFromGroups)
        ;
    } else {
        throw node;
    }
}

/*
 * if [parent] is a goal, adds to [otherTactics]. To add to [userTactics], use
 * [addUserTactic]
 */
function addChild(parent, node) {
    if (isGoal(parent)) {
        // prevent the node addition from changing focus
        if (parent.tacticIndex > 0
            && parent.tacticIndex >=
            parent.userTactics.length + parent.otherTactics.length) {
            parent.tacticIndex++;
        }
        parent.otherTactics.push(node);
    } else if (isTacticGroup(parent)) {
        parent.tactics.push(node);
    } else {
        throw parent;
    }
}

function getClosestGoal(node) {
    if (isGoal(node)) { return node; }
    // if it is not a goal, it ought to have a parent
    if (isTacticGroup(node)) { return node.parent; }
    if (isTactic(node)) {
        if (isGoal(node.parent)) {
            return node.parent;
        } else if (isTacticGroup(node.parent)) {
            return node.parent.parent;
        }
    }
    throw node;
}

function goalNodeUnicityRepr(node) {
    return JSON.stringify({
        "goalTerm": node.goalTerm,
        "hyps": _(node.hyps)
            .map(function(h) {
                return {
                    "hName": h.hName,
                    "hValue": h.hValue,
                    "hType": h.hType,
                };
            })
            .value(),
    });
}

function tacticNodeUnicityRepr(node) {
    return JSON.stringify(
        _(node.goals)
            .map(goalNodeUnicityRepr)
            .value()
    );
}

function getResponseUnfocused(response) {
    return response.rGoals.unfocused;
}

// TODO: I believe there is a danger of race with runTactic
/*
 * @return <Promise>
 */
ProofTree.prototype.runUserTactic = function(t) {
    var self = this;
    var nodeToAttachTo = this.curNode;
    // need to get the status before so that we figure out whether the goal was
    // solved, if only coqtop would tell us...
    var beforeResponse;
    return asyncStatus()
        .then(function(status) {
            beforeResponse = status.response;
            return asyncQueryAndUndo(t);
        })
        .then(function(response) {
            if (isGood(response)) {
                var unfocusedBefore = getResponseUnfocused(beforeResponse);
                var unfocusedAfter = getResponseUnfocused(response);
                var newChild = mkTacticNode(
                    nodeToAttachTo,
                    t,
                    (_.isEqual(unfocusedAfter, unfocusedBefore))
                        ? response.rGoals.focused
                        : []
                );
                nodeToAttachTo.userTactics.unshift(newChild);
                nodeToAttachTo.focusIndex = 0;
                self.update();
                return newChild;
            } else {
                throw response;
                //console.log("Bad response for tactic", t, response);
            }
        })
        .catch(outputError);
}

/*
 * @return <Promise>
 */
ProofTree.prototype.runTactic = function(t, nodeToAttachTo) {

    var self = this;

    var parentGoal = getClosestGoal(nodeToAttachTo);
    var parentGoalRepr = goalNodeUnicityRepr(parentGoal);

    // need to get the status before so that we figure out whether the goal was
    // solved, if only coqtop would tell us...
    var beforeResponse;
    return asyncStatus()
        .then(function(status) {
            beforeResponse = status.response;
            return asyncQueryAndUndo(t);
        })
        .then(function(response) {
            if (isGood(response)) {
                var unfocusedBefore = getResponseUnfocused(beforeResponse);
                var unfocusedAfter = getResponseUnfocused(response);
                var newChild = mkTacticNode(
                    nodeToAttachTo,
                    t,
                    (beforeResponse.rGoals.unfocused.length === response.rGoals.unfocused.length)
                        ? response.rGoals.focused
                        : []
                );

                // only attach the newChild if it produces something
                // unique from existing children
                var newChildRepr = tacticNodeUnicityRepr(newChild);

                var resultAlreadyExists =
                    _(getAllTactics(parentGoal)).some(function(t) {
                        return (tacticNodeUnicityRepr(t) === newChildRepr);
                    })
                ;

                var tacticIsUseless =
                    (newChild.goals.length === 1)
                    && (goalNodeUnicityRepr(newChild.goals[0])
                        === parentGoalRepr)
                ;

                if (!resultAlreadyExists && !tacticIsUseless) {
                    addChild(nodeToAttachTo, newChild);
                    self.update();
                }

            } else {

                //console.log("Bad response for tactic", t, response);

            }

        })
        .catch(outputError);

}

/*
 * @ return <Promise>
 */
ProofTree.prototype.processTactics = function() {

    /*
      every time curNode is changed, the tacticsWorklist should be
      flushed, so that [runTactic] can reliably add the results of running
      the tactic to the current node
    */

    this.onStartProcessing();

    if (_(this.tacticsWorklist).isEmpty()) {
        this.onEndProcessing();
        return Promise.resolve();
    }

    var promiseSpark = this.tacticsWorklist.shift();

    return promiseSpark()
    // delay for testing purposes
        .then(delayPromise(0))
        .then(this.processTactics.bind(this))
        .catch(outputError);

}

/*
 * /!\ assumes the current node is a goal
 * triggers a refreshing of the tactics for the current goal
 */
ProofTree.prototype.refreshTactics = function() {

    var self = this;
    var curNode = this.curNode;

    var tacticsAndGroups =
        _(this.tactics(this))
        .groupBy(function(elt) {
            if ($.type(elt) === "string") {
                return "tactics";
            } else {
                return "groups";
            }
        })
        .value()
    ;

    var tactics = tacticsAndGroups.tactics;

    var tacticSparks = _(tactics)
        .filter(function(t) {
            // TODO: refresh for existential variables
            return (
                !_(self.curNode.userTactics)
                    .concat(self.curNode.otherTactics)
                    .some(function(c) {
                        return (c.tactic === t);
                    })
            );
        })
        .map(function(tactic) {
            return (function() {
                return self.runTactic(tactic, curNode);
            });
        })
        .value()
    ;

    var groups = tacticsAndGroups.groups;

    var groupSparks = _(groups)
        .map(function(group) {
            var groupNode = findOrCreateGroup(curNode, group.name);
            return (
                _(group.tactics)
                    .filter(function(tactic) {
                        return (
                            !_(groupNode.tactics)
                                .some(function(node) {
                                    return (node.tactic === tactic);
                                })
                        );
                    })
                    .map(function(tactic) {
                        return function() {
                            return self.runTactic(tactic, groupNode);
                        }
                    })
                    .flatten(true)
                    .value()
            );
        })
        .flatten(true)
        .value()
    ;

    // flushes the worklist and add the new sparks
    this.tacticsWorklist = tacticSparks.concat(groupSparks);

    this.processTactics();

}

function findOrCreateGroup(goalNode, groupName) {
    var found = _(goalNode.tacticGroups)
        .find(function(tacticGroup) {
            return tacticGroup.name === groupName;
        })
    ;
    if (found !== undefined) { return found; }
    // else, create it
    var groupNode = mkTacticGroupNode(goalNode, groupName);
    goalNode.tacticGroups.push(groupNode);
    return groupNode;
}

function extractGoal(gGoal) {

    if (gGoal.hasOwnProperty("Left")) {
        gGoal = {
            "contents": gGoal.Left,
            "tag": "Raw",
        };
    } else {
        gGoal = gGoal.Right;
    }

    return gGoal;

}

function extractHypothesis(gHyp) {

    if (gHyp.hasOwnProperty("Left")) {
        // this tries to approximate parsing...
        var matches = gHyp.Left.match(/^([\s\S]*) := ([\s\S]*) : ([\s\S]*)$/);
        if (matches !== null) {
            gHyp = {
                "hName": matches[1],
                "hValue": { "contents": matches[2], "tag": "Raw" },
                "hType": { "contents": matches[3], "tag": "Raw" },
            };
        } else {
            matches = gHyp.Left.match(/^([\s\S]*) : ([\s\S]*)$/);
            gHyp = {
                "hName": matches[1],
                "hValue": null,
                "hType": { "contents": matches[2], "tag": "Raw" },
            };
        }
        if (matches == null) {
            console.log("could not extract hypothesis", gHyp);
        }

    } else {
        gHyp = gHyp.Right;
    }

    return gHyp;

}

ProofTree.prototype.hInit = function(response) {

    var self = this;

    if (isBad(response)) {
        console.log(response.rResponse.contents);
        /*
        if (this.onError !== undefined) {
            this.onError(this, response.rResponse.contents);
        }
        */
        return false;
    }

    var goal = response.rGoals.focused[0];

    // There should only be one goal at that point
    this.rootNode = $.extend(
        mkGoalNode(undefined, goal, 0),
        // TODO: check whether this is still needed
        {
            "x0": 0,
            "y0": 0.5,
        }
    );

    // doesn't matter much when this is done, so no chaining
    asyncStatus()
        .then(function(status) {
            self.rootNode.label = status.label;
        })
    ;

    this.curNode = this.rootNode;

    this.refreshTactics();

    this.update();

    return true;

}

function hasParent(n) {
    return n.parent !== undefined;
}
PT.hasParent = hasParent;

function hasGrandParent(n) {
    return hasParent(n) && hasParent(n.parent);
}
PT.hasGrandParent = hasGrandParent;

ProofTree.prototype.curGoal = function() {
    return getClosestGoal(this.curNode);
}

ProofTree.prototype.isCurGoal = function(n) {
    return n.id === this.curGoal().id;
}

ProofTree.prototype.isCurGoalChild = function(n) {
    return hasParent(n) && this.isCurGoal(n.parent);
}

ProofTree.prototype.isCurGoalGrandChild = function(n) {
    return hasParent(n) && this.isCurGoalChild(n.parent);
}

ProofTree.prototype.isRootNode = function(n) {
    return n.id === this.rootNode.id;
}

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
                else if (sameNode(tgt, this.hoveredNode.parent)) {
                    return thick;
                }
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
        var focusedChild = this.getFocusedChild(this.curNode);
        if (focusedChild === undefined) { return thin; }
        if (this.isCurNode(src) && focusedChild.id === tgt.id) { return thick; }
        // we want to thicken the path to the focused subgoal
        var focusedGrandChild = this.getFocusedChild(focusedChild);
        if (focusedGrandChild === undefined) { return thin; }
        if (focusedChild.id == src.id && focusedGrandChild.id === tgt.id) {
            return thick;
        }
        return thin;
    } else if (isTacticish(this.curNode)) {
        var focusedChild = this.getFocusedChild(this.curNode);
        if (focusedChild !== undefined && tgt.id === focusedChild.id) {
            return thick;
        }
        return thin;
    } else {
        throw this.curNode;
    }
}

// [nodeDOM] is the DOM foreignObject, [d] is the node in the tree structure
ProofTree.prototype.updateNodeMeasures = function(nodeDOM, d) {
    var elementToMeasure =
        isGoal(d)
        ? nodeDOM // get the foreignObject itself
        : nodeDOM.firstChild // get the span
    ;
    // we save in the rect field the size of the text rectangle
    var rect = elementToMeasure.getBoundingClientRect();
    d.width = this.nodeWidth(d);
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
        .selectAll(function() {
            return this.getElementsByTagName("foreignObject");
        })
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
    // the goal nodes need to be rendered at fixed width goalWidth
    // the tactic nodes will be resized to their actual width later
        .attr("width", function(d) {
            return isGoal(d) ? self.goalWidth : self.tacticWidth;
        })
    ;

    textEnter
        .append("xhtml:body")
        //.classed("svg", true)
        .style("padding", function(d) {
            return isGoal(d) ? goalBodyPadding + "px" : "0px 0px";
        })
        .style("background-color", "rgba(0, 0, 0, 0)")
    // should make it less painful on 800x600 videoprojector
    // TODO: fix computing diffs so that zooming is possible
        .style("font-size", (this.width < 1000) ? "12px" : "14px")
        .style("font-family", "monospace")
        .each(function(d) {
            var jqBody = $(d3.select(this).node());
            var jQContents;
            if (isTactic(d)) {
                d.span = $("<div>")
                    .addClass("tacticNode")
                    .css("padding", "4px")
                    .text(d.tactic);
                jQContents = d.span;
            } else if (isTacticGroup(d)) {
                return; // needs to be refreshed on every update, see below
            } else if (isGoal(d)) {
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
                d.goalSpan = $("<span>").html(showTerm(d.goalTerm));
                jQContents.append(d.goalSpan);
            } else {
                throw d;
            }
            jqBody.append(jQContents);
        })
    ;

    textSelection
    // the tactic groups need to be updated every time
        .each(function(d) {
            var jqBody = $(d3.select(this).select("body").node());
            var jQContents;
            if (isTacticGroup(d)) {
                var focusedTactic = d.tactics[d.tacticIndex];
                var nbTactics = d.tactics.length;
                var counterPrefix = (
                    (nbTactics > 1)
                        ? '[' + (d.tacticIndex + 1) + '/' + d.tactics.length + ']<br/>'
                        : ''
                );
                d.span = $("<div>")
                    .addClass("tacticNode")
                    .css("padding", "4px")
                    .html(
                        (self.isCurNodeChild(d))
                            ? counterPrefix + focusedTactic.tactic
                            : focusedTactic.tactic
                    );
                jQContents = d.span;
                jqBody.empty();
                jqBody.append(jQContents);
            } else if (isGoal(d)) {
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
                d.goalSpan = $("<span>").html(showTerm(d.goalTerm));
                jQContents.append(d.goalSpan);
                jqBody.empty();
                jqBody.append(jQContents);
            }
        })
        .each(function(d) {
            var nodeDOM = d3.select(this).node();
            self.updateNodeMeasures(nodeDOM, d);
        })
        // preset the width to update measures correctly
        .attr("width", function(d) {
            return isGoal(d) ? self.goalWidth : self.tacticWidth;
        })
        .attr("height", 0)
        .each(function(d) {
            var nodeDOM = d3.select(this).node().firstChild;
            self.updateNodeMeasures(nodeDOM, d);
        })
    ;

    // Now that the nodes have a size, we can compute the factors

    var curGoal = this.curGoal();
    var visibleChildren = _(self.getViewChildren(curGoal));
    var visibleGrandChildren = _(self.getViewGrandChildren(curGoal));
    var visibleNodes = _([]);
    if (hasParent(curGoal)) {
        visibleNodes = visibleNodes.concat([curGoal.parent]);
    }
    visibleNodes = visibleNodes.concat([curGoal]);
    visibleNodes = visibleNodes.concat(visibleChildren.value());
    visibleNodes = visibleNodes.concat(visibleGrandChildren.value());
    var minXNode = _(visibleNodes).min(nodeX).value();
    var maxXNode = _(visibleNodes).max(nodeX).value();
    var minX = nodeX(minXNode), maxX = nodeX(maxXNode);
    var dX = maxX - minX;

    /*
      we want: width = goalWidth/2 + xFactor * dX + goalWidth/2
    */
    this.xFactor = dX === 0
        ? this.width
        : (this.width - minXNode.width / 2 - maxXNode.width / 2) / dX
    ;

    /*
      we want all visible grand children to be apart from each other
      i.e.
      ∀ a b, yFactor * | a.y - b.y | > a.height/2 + b.height/2 + nodeVSpacing
      we also want all visible children to be apart from each other (especially
      when they don't have their own children to separate them)
    */
    var gcSiblings = _.zip(
        visibleGrandChildren.value(),
        visibleGrandChildren.rest().value()
    );
    gcSiblings.pop(); // removes the [last, undefined] pair at the end
    var cSiblings = _.zip(
        visibleChildren.value(),
        visibleChildren.rest().value()
    );
    cSiblings.pop();
    // also, the current node should not overlap its siblings
    var currentSiblings = [];
    if (isGoal(this.curNode) && hasParent(this.curNode)) {
        var curNodeSiblings = _(self.getViewChildren(this.curNode.parent));
        currentSiblings = _.zip(
            curNodeSiblings.value(),
            curNodeSiblings.rest().value()
        );
        currentSiblings.pop();
    }
    var siblings = _(gcSiblings.concat(cSiblings, currentSiblings));
    var yFactors = siblings
        .map(function(e) {
            var a = e[0], b = e[1];
            var yDistance = nodeY(b) - nodeY(a);
            var wantedSpacing = ((a.height + b.height) / 2) + nodeVSpacing;
            return wantedSpacing / yDistance;
        })
        .value()
    ;
    this.yFactor = _.isEmpty(yFactors) ? this.height : _.max(yFactors);

    /*
      here we are looking for the descendant which should align with the current
      node. it used to be at the top of the view, now it's centered.
     */
    var centeredDescendant = undefined;
    if (isGoal(this.curNode)) {
        var centeredTactic = this.getFocusedChild(this.curNode);
        if (centeredTactic !== undefined) {
            centeredDescendant = this.getFocusedChild(centeredTactic);
            if (centeredDescendant === undefined) {
                centeredDescendant = centeredTactic;
            }
        }
    }  else if (isTacticish(this.curNode)) {
        var t = getTacticFromTacticish(this.curNode);
        if (t.goals.length > 0) {
            centeredDescendant = t.goals[t.goalIndex];
        }
    } else {
        throw this.curNode;
    }

    if (centeredDescendant !== undefined) {
        if (isGoal(this.curNode) && isGoal(centeredDescendant)) {
            // computing the difference in height between the <hr> is not
            // obvious...
            var hrDelta =
                this.curNode.goalSpan[0].offsetTop
                - centeredDescendant.goalSpan[0].offsetTop
            ;
            this.descendantsOffset =
                this.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
                - (curGoal.height - centeredDescendant.height) / 2
                + hrDelta
            ;
        } else if (isTacticish(this.curNode)) {
            var hrDelta =
                this.curNode.parent.goalSpan[0].offsetTop
                - centeredDescendant.goalSpan[0].offsetTop
            ;
            this.descendantsOffset =
                this.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
                - (curGoal.height - centeredDescendant.height) / 2
                + hrDelta
            ;
        } else {
            this.descendantsOffset =
                this.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
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
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .transition()
        .duration(animationDuration)
        .style("opacity", "1")
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

                    asyncLog("CLICK " + nodeString(d));

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
        .classed("tactic", isTacticish)
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .attr("x", function(d) { return d.cX0; })
        .attr("y", function(d) { return d.cY0; })
        .attr("rx", function(d) { return isGoal(d) ? 0 : 10; })
    ;

    rectSelection
        .classed("current", function(d) { return self.isCurNode(d); })
        .classed("solved", function(d) { return d.solved; })
        .transition()
        .duration(animationDuration)
        .style("opacity", "1")
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
        .style("opacity", 1)
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
        .attr("transform",
              "translate(" + self.viewportX + ", " + self.viewportY + ")"
             )
    ;

    var diffSelection = this.diffLayer.selectAll("g.node-diff").data(
        // only goal nodes with a grandparent give rise to a diff
        _(nodes).filter(function(d) {
            return isGoal(d) && hasGrandParent(d);
        }).value(),
        byNodeId
    );

    diffSelection.enter()
        .append("g")
        .classed("node-diff", true)
        .classed("diff", true)
    ;

    diffSelection
    // need to redo this every time now that nodes can change :(
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
                d3.select(this)
                .selectAll("g.diff-item")
                .data(diffList, byDiffId)
            ;

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
                        if (JSON.stringify(oldHyp.hType)
                            !== JSON.stringify(newHyp.hType)) {
                            d3this
                                .append("path")
                                .attr("fill", diffBlue)
                                .attr("stroke", blueStroke)
                                .attr("opacity", diffOpacity)
                            ;

                            var subdiff = spotTheDifferences(
                                oldHyp.div,
                                newHyp.div
                            );

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
            var focusChild = self.getFocusedChild(gp);
            var focusGrandChild = (focusChild === undefined)
                ? undefined
                : self.getFocusedChild(focusChild)
            ;
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

    if (callback !== undefined) { callback(); }

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

ProofTree.prototype.shiftPrevByTacticGroup = function(n) {
    if (this.paused) { return; }
    var self = this;
    if (n.solved) { return; }
    if (isGoal(n)) {
        if (n.tacticIndex > 0) {
            n.tacticIndex--;
            asyncLog("UPGROUP " + nodeString(self.getViewChildren(n)[n.tacticIndex]));
            self.update();
        }
    } else {
        throw n;
    }
}

ProofTree.prototype.shiftNextByTacticGroup = function(n) {
    if (this.paused) { return; }
    var self = this;
    if (n.solved) { return; }
    var viewChildren = this.getViewChildren(n);
    if (isGoal(n)) {
        if (n.tacticIndex + 1 < viewChildren.length) {
            n.tacticIndex++;
            asyncLog("DOWNGROUP " + nodeString(viewChildren[n.tacticIndex]));
            self.update();
        }
    } else {
        throw n;
    }
}

/* assumes [n] is tacticish */
ProofTree.prototype.shiftPrevGoal = function(n) {
    if (this.paused) { return; }
    var self = this;
    if (isTactic(n)) {
        if (n.goalIndex > 0) {
            n.goalIndex--;
            self.update();
        }
    } else if (isTacticGroup(n)) {
        this.shiftPrevGoal(getTacticFromGroup(n));
    } else {
        throw n;
    }
}

/* assumes [n] is tacticish */
ProofTree.prototype.shiftNextGoal = function(n) {
    if (this.paused) { return; }
    var self = this;
    if (isTactic(n)) {
        if (n.goalIndex < n.goals.length - 1) {
            n.goalIndex++;
            self.update();
        }
    } else if (isTacticGroup(n)) {
        this.shiftNextGoal(getTacticFromGroup(n));
    } else {
        throw n;
    }
}

/*
ProofTree.prototype.shiftPrevBySubgoal = function(n) {
    if (this.paused) { return; }
    var self = this;
    function tryShifting(n) {
        if (n.focusIndex> 0) {
            n.focusIndex--;
            asyncLog("UP " + nodeString(n.allChildren[n.focusIndex]));
            self.update();
            return true;
        }
        return false;
    }
    if (n.solved) { return; }
    if (isGoal(n) && n.allChildren.length > 0) {
        tryShifting(n.allChildren[n.focusIndex]) || tryShifting(n);
    } else {
        tryShifting(n);
    }
}

ProofTree.prototype.shiftNextBySubgoal = function(n) {
    if (this.paused) { return; }
    var self = this;
    function tryShifting(n) {
        if (n.focusIndex + 1 < self.getViewChildren(n).length) {
            n.focusIndex++;
            asyncLog("DOWN " + nodeString(n.allChildren[n.focusIndex]));
            self.update();
            return true;
        }
        return false;
    }
    if (n.solved) { return; }
    if (isGoal(n) && n.allChildren.length > 0) {
        tryShifting(n.allChildren[n.focusIndex]) || tryShifting(n);
    } else {
        tryShifting(n);
    }
}
*/

ProofTree.prototype.click = function(d, remember, callback) {

    var self = this;

    if (this.paused) { return; }

    makeFocusedTwoGenerations(d);

    if (d.solved) {
        if (hasParent(d)) {
            this.click(d.parent, remember, callback);
        }
        return;
    }

    // when the user clicks on a tactic node below
    // bring them to the first unsolved goal instead
    /*
    var viewChildren = this.getViewChildren(d);
    if (isTacticish(d)
        && d.depth > this.curNode.depth
        && viewChildren.length > 0) {
        expand(d);
        var firstUnsolved = _(viewChildren)
            .find(function(e) { return !e.solved; });
        if (firstUnsolved !== undefined) {
            this.click(firstUnsolved, remember, callback);
            return;
        }
    }
    */
    // when the user clicks on the parent tactic, bring them back to its parent
    // DO NOT WANT ANYMORE! This will discard things! :(
    /*
    if (isTacticish(d) && d.depth < this.curNode.depth) {
        this.click(d.parent, remember, callback);
        return;
    }
    */

    // when the user goes back to a parent tactic, if it only has one subgoal,
    // it must probably mean the user wants to cancel the tactic altogether, so
    // backtrack once more to the previous goal
    if (isTacticish(d)
        && d.depth < this.curNode.depth
        && getTacticFromTacticish(d).goals.length === 1) {
        this.click(d.parent, remember, callback);
        return;
    }

    this.navigateTo(d, false)
        .then(function() {
            if (isGoal(d)) {
                self.refreshTactics();
            } if (isTactic(d)) {
                if (isTerminating(d)) {
                    self.solved(d);
                }
            } else if (isTacticGroup(d)) {
                var tactic = getTacticFromGroup(d);
                if (_.isEmpty(tactic.goals)) {
                    self.solved(tactic);
                }
            }
            expand(d);
            self.update(callback);
        })
        .catch(outputError);

}

// called when n has been solved
ProofTree.prototype.solved = function(n) {
    var self = this;
    n.solved = true;
    if (isTacticGroup(n)) {
        getTacticFromGroup(n).solved = true;
    }
    collapse(n);
    if (hasParent(n)) {
        this.navigateTo(n.parent, true)
            .then(function() {
                window.setTimeout(function () {
                    self.childSolved(n.parent);
                    self.update();
                }, animationDuration);
            })
            .catch(outputError);
    } else {
        window.setTimeout(function () {
            asyncLog("QED " + JSON.stringify(PT.proofFrom(self.rootNode)));
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
            _(this.getViewChildren(n))
            .every(function(n) { return n.solved === true; })
        ;
        if (lastSubgoal) {
            this.solved(n);
        } else {
            var t = getTacticFromTacticish(n);
            t.goalIndex = _(t.goals)
                .findIndex(function(g) { return !g.solved; })
            ;
        }
    }
}

function collapse(d) { d.collapsed = true; }

function collapseChildren(d) {
    _(d.children).forEach(collapse);
}

function expand(d) {
    d.collapsed = false;
    if (isGoal(d)) {
        _(d.userTactics).each(expand);
        _(d.otherTactics).each(expand);
        _(d.tacticGroups).each(expand);
    } else if (isTacticGroup(d)) {
        _(d.tactics).each(expand);
    } else if (isTactic(d)) {
        // nothing
    } else {
        throw d;
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
    if (tacNode.children.length <= 1) {
        if (!hasGrandParent(tacNode)) { return 0; }
        return 1 + depthSolved(tacNode.parent.parent);
    } else {
        return 0;
    }
}

function sequencePromises(accumulatedPromises, newPromise) {
    return accumulatedPromises.then(newPromise);
}

function isTerminating(tactic) {
    var tactic = getTacticFromTacticish(tactic);
    return _.isEmpty(tactic.goals);
}

/*
 * @return <Promise>
 */
ProofTree.prototype.navigateTo = function(dest, bubblingFromSolved) {

    var self = this;

    // if we are going to move, flush the worklist before anything happens
    if (this.curNode.id !== dest.id) {
        this.tacticsWorklist = [];
    }

    var p = path(this.curNode, dest);
    // morally, q = [ [p0, p1], [p1, p2], ... ]
    var q = _.zip(p, _(p).rest().value());
    q.pop(); // remove the extra [p_last, undefined] at the end

    // this will build a promise, trust me, I promise ;D
    return _(q)
    // building a list of functions return a promise
        .map(function(elt) {
            var src = elt[0];
            var dst = elt[1];
            var goingUp = src.depth > dst.depth;

            // this function must return a Promise
            return function() {
                if (goingUp) {
                    collapseChildren(src);
                    // when leaving a goal, hide its tactics
                    if (isGoal(src)) { collapse(src); }
                    /*
  Here are the different cases:
  tactic <- goal
  tacticgroup <- goal
  goal <- tactic
  tacticgroup <- tactic
  goal <- tacticgroup

When leaving a goal, it should be collapsed.
When arriving to a tactic, it should be refreshed.
When arriving to a goal from a tactic or tacticgroup, the tactic's goals should be reset.
*/

                    if (isGoal(dst)) {
                        // if we are going up because a subgoal was proved, no backtracking
                        if (bubblingFromSolved) {
                            return Promise.resolve();
                        }

                        // otherwise, user abandoned a tactic, restore its original state
                        var t = getTacticFromTacticish(src);
                        t.goals = _(t.originalGoals)
                            .map(_.partial(mkGoalNode, t))
                            .value()
                        ;
                        t.goalIndex = 0;

                        // and backtrack
                        return asyncStatus()
                            .then(function(response) {
                                return asyncRewind(response.label - dst.label);
                            })
                        ;
                    }

                    if (isTacticish(dst)) {
                        if (!bubblingFromSolved) {
                            return Promise.resolve();
                        }

                        return asyncStatus()
                            .then(function(status) {
                                var response = status.response;
                                // Here, we update the goal nodes, because
                                // existential variables might have been
                                // resolved
                                _(getTacticFromTacticish(dst).goals)
                                    .filter(function(goal) {
                                        return !goal.solved;
                                    })
                                    .each(function(goal, index) {
                                        updateGoalNode(goal, response.rGoals.focused[index]);
                                    });
                            })
                        ;
                    }

                    throw dst;

                } else { // going down
                    // hide sibling tactic nodes
                    if (isGoal(src)) { collapse(src); }
                    if (isGoal(dst)) {
                        // need to focus on the subgoal index according to how
                        // many subgoals are left...
                        var nbSubgoalsDone = _(getTacticFromTacticish(src).goals)
                            .filter(function(g) { return g.solved; })
                            .size()
                        ;
                        var indexToFocus = dst.ndx - nbSubgoalsDone;
                        return asyncQuery('Focus ' + indexToFocus + '.')
                            .then(asyncStatus)
                            .then(function(status) {
                                console.log("Focused goal, now at label", status.label);
                                dst.label = status.label;
                            });
                    } else if (isTactic(dst)) {
                        return asyncQuery(dst.tactic);
                    } else if (isTacticGroup(dst)) {
                        var tactic = getTacticFromGroup(dst);
                        return asyncQuery(tactic.tactic);
                    } else {
                        throw dst;
                    }
                }
            };
        })
    // process the promises in sequential order
        .reduce(sequencePromises, Promise.resolve())
        .then(function() {
            self.curNode = dest;
            return Promise.resolve();
        })
        .catch(outputError)
    ;

}

function isGoal(node) {
    if (node === undefined) {
        throw node;
    }
    return node.type === "goal";
}
function isTactic(node) { return node.type === "tactic"; }
function isTacticGroup(node) { return node.type === "tacticgroup"; }
function isTacticish(node) { return isTactic(node) || isTacticGroup(node); }

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

                case "Exists":
                    alert("TODO: Exists annotateTerm");
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
                    alert("UNKNOWN TAG: " + t.tag);
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
    if (keyboardPaused) { return; }
    if (activeProofTree !== undefined) {
        activeProofTree.keydownHandler.call(activeProofTree);
    }
    keyboardPaused = true;
    window.setTimeout(function() { keyboardPaused = false; }, keyboardDelay);
}

ProofTree.prototype.keydownHandler = function() {

    // don't interact while typing
    if (d3.event.target.type === "textarea") { return; }

    var curNode = this.curNode;

    var children = this.getViewChildren(curNode);

    this.usingKeyboard = true;

    //console.log(d3.event.keyCode);

    switch (d3.event.keyCode) {

    case 37: // Left
    //case 65: // a
        d3.event.preventDefault();
        if (hasParent(curNode)) {
            asyncLog("LEFT " + nodeString(curNode.parent));
            this.click(curNode.parent);
        }
        break;

    case 39: // Right
    //case 68: // d
        d3.event.preventDefault();
        var dest = this.getFocusedChild(curNode);
        if (dest === undefined) { break; }
        var viewChildren = this.getViewChildren(dest);
        if (isGoal(curNode) && viewChildren.length > 0) {
            // try to actually reach the focused subgoal
            dest = this.getFocusedChild(dest);
        }
        if (dest !== undefined) {
            asyncLog("RIGHT " + nodeString(dest));
            this.click(dest);
        }
        break;

    case 38: // Up
    //case 87: // w
        d3.event.preventDefault();
        if (isGoal(curNode)) {
            this.shiftPrevByTacticGroup(curNode);
        } else if (isTacticish(curNode)) {
            this.shiftPrevGoal(curNode);
        } else {
            throw curNode;
        }
        break;

    case 40: // Down
    //case 83: // s
        d3.event.preventDefault();
        if (isGoal(curNode)) {
            this.shiftNextByTacticGroup(curNode);
        } else if (isTacticish(curNode)) {
            this.shiftNextGoal(curNode);
        } else {
            throw curNode;
        }
        break;

    case 219: // [
        var focusedChild = this.getFocusedChild(curNode);
        if (isTacticGroup(focusedChild)) {
            if (focusedChild.tacticIndex > 0) {
                focusedChild.tacticIndex--;
                this.update();
            }
        }
        break;

    case 221: // ]
        var focusedChild = this.getFocusedChild(curNode);
        if (isTacticGroup(focusedChild)) {
            if (focusedChild.tacticIndex < focusedChild.tactics.length - 1) {
                focusedChild.tacticIndex++;
                this.update();
            }
        }
        break;

        /*
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
        */

    default:
        //console.log("Unhandled event", d3.event.keyCode);
        return;
    }

    // EDIT: now that we integrate the proof tree, it's best to let stuff bubble up
    // if we haven't returned, we don't want the normal key behavior
    //d3.event.preventDefault();

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
        var allTactics = getAllTactics(t);
        // if one of the subgoals is solved, find it and return its proof
        var solution = _(allTactics).find("solved");
        if (solution !== undefined) {
            return this.partialProofFrom(solution, indentation);
        }
        // otherwise, try to see if a partial path was recorded
        var partial = _(allTactics).find(function(n) {
            return n.hasOwnProperty("partial");
        });
        if (partial !== undefined) {
            return this.partialProofFrom(partial, indentation);
        }
        // otherwise, try to find a node in the ancestor tree of the current
        var viewChildren = this.getViewChildren(t);
        var curTac = _(viewChildren).find(function(n) {
            return self.isCurNodeAncestor(n);
        });
        if (curTac !== undefined) {
            return this.partialProofFrom(curTac, indentation);
        }
        // otherwise, make the appropriate textarea
        if (this.isCurNode(t)) {
            var result = $("<span>");
            var ta = $("<textarea>")
                .addClass("resizeWidth")
                .addClass("resizeHeight")
                .addClass("activeTextarea")
                .css("background-color", "#CB99C9")
                .css("min-height", "22px")
                .css("min-width", "22px")
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
                    .css("height", "22px")
                    .text("OK")
                    .click(function() {

                        var tactic = ta.val();

                        asyncLog("MANUALTACTIC " + tactic);

                        // if the tactic is already here, just click it
                        var existingTactic = _(getAllTactics(self.curNode))
                            .find(function(elt) {
                                return elt.tactic === tactic;
                            })
                        ;
                        if (existingTactic !== undefined) {
                            self.click(existingTactic);
                            return;
                        } else {
                            // otherwise, need to run the tactic
                            self.runUserTactic(tactic)
                                .then(function(newNode) {
                                    self.click(newNode);
                                })
                                .catch(function(error) {
                                    // TODO: not use alert
                                    alert(error.rResponse.contents);
                                });
                        }

                    })
            );
            return result;
        } else {
            var ta = $("<textarea>")
                .addClass("resizeWidth")
                .addClass("resizeHeight")
                .css("min-height", "22px")
                .css("min-width", "22px")
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
    else if (isTactic(t)) {
        var t = getTacticFromTacticish(t);
        var result = span(t.tactic);
        if (t.goals.length === 1) {
            _(t.goals).each(function(e) {
                result.append(document.createTextNode(" "));
                result.append(self.partialProofFrom(e, indentation));
            });
        } else {
            _(t.goals).each(function(e) {
                var subproof = $("<div>");
                subproof.append(span(indent + "{" + nbsp));
                subproof.append(
                    $("<span>").append(self.partialProofFrom(e, indentation + 1))
                );
                // should be div if the proof has branching
                subproof.append(span(" }"));
                result.append(subproof);
            });
        }
        return result;
    } else if (isTacticGroup(t)) {
        var tactic = getTacticFromGroup(t);
        return this.partialProofFrom(tactic, indentation);
    } else {
        throw t;
    }

}

// returns a text proof
PT.proofFrom = function(t) {
    if (isGoal(t)) {
        return PT.proofFrom(_(getAllTactics(t)).find("solved"));
    } else if (isTacticish(t)) {
        t = getTacticFromTacticish(t);
        return [
            t.tactic,
            _(t.goals).map(PT.proofFrom).value(),
        ];
    } else {
        throw t;
    }
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

/*
 * @return <Promise>
 */
ProofTree.prototype.replayThisProof = function(proof) {

    var self = this;

    if (_.isEmpty(proof)) {
        return Promise.resolve();
    } else {
        var fst = proof[0];
        var snd = proof[1];
        return asyncQuery(fst)
            .then(function(response) {
                if (isGood(response)) {
                    // we want to replay the proof as we typeset it, so that the
                    // proof process stays in sync with the text produced
                    // therefore, we need to focus when the text would focus
                    var needToFocus = snd.length > 1;
                    return _(snd)
                        .map(function(n) {
                            return function() {
                                if (needToFocus) {
                                    return asyncQuery(" { ")
                                        .then(function() { return self.replayThisProof(n); })
                                        .then(function() { return asyncQuery(" } "); })
                                        .catch(outputError)
                                    ;
                                } else {
                                    return self.replayThisProof(n);
                                }
                            };
                        })
                        .reduce(sequencePromises, Promise.resolve())
                    ;
                } else {
                    console.log("Replay failed on applying " + fst);
                    console.log("Error: " + contents(response));
                    throw new Error("Replay failed, see log");
                }
            })
            .catch(outputError)
        ;
    }

}

ProofTree.prototype.proof = function() {
    return PT.proofFrom(this.rootNode);
}

/*
 * @return <Promise>
 */
ProofTree.prototype.replay = function() {
    return this.replayThisProof(PT.proofFrom(this.rootNode));
}

ProofTree.prototype.qed = function() {
    asyncQuery("Qed.")
        .then(function(response) {
            if (isBad(response)) {
                console.log("Qed failed, error:" + contents(response));
            }
        })
        .catch(outputError)
    ;
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
    if (t.length === 1) { return ' ' + showBinder(t[0]);  }
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

function showName(t) {
    if (t === null) { // underscore
        return ident('_');
    } else {
        return ident(t);
    }
}

function showNames(t) {
    if (_.isEmpty(t)) { return ""; }

    return showName(t[0]) + " " + showNames(_(t).rest().value());
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

    case "Raw":
        return '<span>' + c + '</span>';

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
            syntax("∀") + showBinders(c[0]) + syntax(",")
                + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
                + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Lambda":
        return par(
            precForall,
            syntax("λ") + showBinders(c[0]) + syntax(",")
                + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
                + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Exists":
        return par(
            precForall,
            syntax("∃") + showBinders(c[0]) + syntax(",")
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
    var minimalWidth = 22;
    var minimalHeight = 22;
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
                {'width': Math.max(hiddenDiv.width() + 2, minimalWidth) + 'px'},
                duration
            );
        }
        if ($(this).hasClass("resizeHeight")) {
            $(this).animate(
                {'height': Math.max(hiddenDiv.height() + 2, minimalHeight) + 'px'},
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

var lastDebugId = undefined;

ProofTree.prototype.updateDebug = function() {

    var debugWidth = this.width / 2;

    this.debug
        .selectAll(function() { return this.getElementsByTagName("foreignObject"); })
        .attr("width", debugWidth + "px")
    ;
    this.debug.select("rect").attr("width", debugWidth + "px");

    // avoid recomputing debug when user has not moved
    if (this.curNode.id !== lastDebugId) {

        lastDebugId = this.curNode.id;

        var debugDiv = this.debug.select('div');
        var jDebugDiv = $(debugDiv[0]);

        var partialProof = this.partialProofFrom(this.rootNode, 1);

        jDebugDiv.empty();
        jDebugDiv.css("height", ""); // removing it so that it recomputes
        jDebugDiv.append($("<div>").text(this.theorem));
        jDebugDiv.append($("<div>").text("Proof."));
        partialProof.prepend(span("&nbsp;&nbsp;")); // initial indentation
        jDebugDiv.append(partialProof);
        //$(".resizeWidth, .resizeHeight").change();
        jDebugDiv.append($("<div>").text("Qed."));

    }

    updateNodeHeight(this.debug, Math.floor(this.height / 3));

}

function updateNodeHeight(selector, maxHeight) {

    var div = selector.select('div');

    selector
    // Webkit bug, cannot selectAll on camel case names :(
        .selectAll(function() {
            return this.getElementsByTagName("foreignObject");
        })
        .attr("height", function() {
            var height = div[0][0].getBoundingClientRect().height;
            var desiredHeight = Math.min(height, maxHeight);
            $(this).css("height", desiredHeight + "px");
            $(div[0][0]).css("height", desiredHeight + "px");
            selector
                .select("rect")
                .attr("height", desiredHeight + "px")
            ;
            return desiredHeight + "px";
        })
    ;

    var jDiv = $(div[0]);
    var button = jDiv.find("button");
    if (button.length !== 0) {
        var topMargin = 60; // somewhat arbitrary, should be about 2 lines
        jDiv.scrollTop(
            jDiv.scrollTop() - jDiv.offset().top + button.offset().top - topMargin
        );
    }

}

/*
 * @return <Promise>
 */
function debugStatus() {
    return asyncStatus()
        .then(function(status) { console.log(status); })
        .catch(outputError)
    ;
}

// specialized version of console.log, because JS is stupid
function outputError(error) {
    console.log(error.stack);
}

function delayPromise(time) {
    return function(result) {
        return new Promise(function(onFulfilled, onRejected) {
            window.setTimeout(function() { onFulfilled(result); }, time);
        });
    }
}

function showNode(n) {
    var res = "{ type : " + n.type + ", contents: ";
    if (isGoal(n)) {
        res += n.goalString;
    } else if (isTacticish(n)) {
        res += getTacticFromTacticish(n).tactic;
    }
    res += " }";
    return res;
}
