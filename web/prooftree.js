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
var animationDuration = 200;
var keyboardDelay = 100;
var keyboardPaused = false;
var autoLayout = true;

$(document).ready(function() {

    setupTextareaResizing();

    $(document)
        .on('mouseenter mouseover', '.term', function(e){
            $(this).find("*").andSelf().each(function() {
                $(this).data('background-color', $(this).css('background-color'));
                $(this).css('background-color', 'white');
            });
            e.stopImmediatePropagation();
        })
        .on('mouseout mouseleave', '.term', function(e){
            $(this).find("*").andSelf().each(function() {
                $(this).css('background-color', $(this).data('background-color'));
            });
            e.stopImmediatePropagation();
        })
    ;

});

var diffRed   = "#EE8888";
var diffGreen = "#88EE88";
var diffBlue  = "#8888EE";
var diffOrange = "#FFB347";
var diffOpacity = 0.75;
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

/*
  The following DOM is constructed from the given anchor:

anchor
`- div id="pt-n"
   `- svg id="svg-n"
      `- script xhref="SVGPan.js"
      `- g id="viewport"            pannable and zoomable (SVGPan.js)
      |  `- g id="link-layer"
      |  `- g id="rect-layer"
      |  `- g id="diff-layer"
      |  `- g id="text-layer"

*/
// [anchor] is a native DOM element
function ProofTree(anchor, width, height,
                   onStartProcessing, onEndProcessing) {

    var self = this;

    this.anchor = d3.select(anchor);
    this.width = width;
    this.height = height;
    this.onStartProcessing = onStartProcessing;
    this.onEndProcessing = onEndProcessing;

    this.paused = false;
    this.svgId = _.uniqueId();
    this.xFactor = this.width;
    this.yFactor = this.height;
    this.userState = {};
    this.usingKeyboard = true; // true until the user moves their mouse
    this.goalWidth = computeGoalWidth(this.width);
    this.tacticWidth = computeTacticWidth(this.width);

    this.tree = d3.layout.tree()
        .children(function(node) {
            // fake nodes are used to trick the layout engine into spacing
            // childrenless nodes appropriately
            if (node.type === 'fake') { return []; }
            var viewChildren = node.getViewChildren();
            if (viewChildren === undefined) {
                throw node;
            }
            // in order to trick d3 into displaying tactics better add fake
            // children to tactic nodes that solve their goal
            if (isTacticish(node) && viewChildren.length === 0) {
                return [{ 'id' : _.uniqueId(), 'type': 'fake' }];
            }
            return viewChildren;
        })
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
            if ($(":focus").size() === 0) {
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
    // also need these as attributes for svg_todataurl
        .attr("width", this.width + "px")
        .attr("height", this.height + "px")
        //.attr("focusable", true)
    // this creates a blue outline that changes the width weirdly
    //.attr("tabindex", 0)
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
    // also need these as attr for svg_todataurl
    this.svg.attr("width", this.width + "px");
    this.svg.attr("height", this.height + "px");
    this.goalWidth = computeGoalWidth(this.width);
    this.tacticWidth = computeTacticWidth(this.width);
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

var diffColor = (function() {
    var colors = [
        "#ffbb78",
        "#f7b6d2",
        "#dbdb8d",
        "#6b6ecf",
        "#8ca252",
        "#b5cf6b",
        "#cedb9c",
        "#bd9e39",
        "#d6616b",
        "#ce6dbd",
        "#de9ed6",
    ];
    var scale = d3.scale.ordinal().range(colors);
    return function(n) {
        return scale(n);
    };
})();

/*
  This might be terrible design, but [spotTheDifference] currently marks inline
  diffs through CSS background-color. It's much more stable than using
  rectangles when animated.
 */
function spotTheDifferences(before, after) {

    function rec(before, after) {

        var nbBefore = before.children().length;
        var nbAfter  =  after.children().length;
        if (nbBefore !== nbAfter) {
            return [{
                "removed": before,
                "added": after,
            }];
        }

        var nbChildren = nbBefore;
        if (nbChildren === 0) { // both leaves
            if (before.html() !== after.html()) {
                return [{
                    "removed": before,
                    "added": after,
                }];
            } else {
                return [];;
            }
        }

        var everyChildChanged = true;

        var childrenChanges = _.range(nbChildren).reduce(function(acc, i) {
            var tmp = rec($(before.children()[i]), $(after.children()[i]));
            if (tmp.length === 0) { everyChildChanged = false; }
            return acc.concat(tmp);
        }, [])
        ;

        if (everyChildChanged) {
            return [{
                "removed": before,
                "added": after,
            }];
        } else {
            return childrenChanges;
        }

    }

    var removed = [];
    var added = [];

    _(rec($(before).children(), $(after).children())).each(function(pair, ndx) {
        pair.removed.css("background-color", diffColor(ndx));
        pair.added.css("background-color", diffColor(ndx));
        //removed.push(pair.removed);
        //added.push(pair.added);
    });

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

function emptyRect0(node, currentY) {
    var delta = 1; // how big to make the empty rectangle
    return $.extend(
        {
            "left": node.cX0,
            "right": node.cX0 + node.width,
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

ProofTree.prototype.isFocusedGoal = function(d) {
    var focusedGoal = this.getFocusedGoal();
    if (focusedGoal === undefined) { return false; }
    return d.id === focusedGoal.id;
}

ProofTree.prototype.getFocusedGoal = function() {
    var focusedChild = this.curNode.getFocusedChild();
    if (focusedChild !== undefined) {
        if (isGoal(focusedChild)) { return focusedChild; }
        focusedChild = focusedChild.getFocusedChild();
        if (focusedChild !== undefined) {
            return focusedChild;
        }
    }
    return undefined;
}

ProofTree.prototype.isFocusedChild = function(d) {
    var focusedChild = this.curNode.getFocusedChild();
    return (focusedChild !== undefined && d.id === focusedChild.id);
}

ProofTree.prototype.xOffset = function(d) {
    return - d.nodeWidth() / 2; // position the center
}

ProofTree.prototype.yOffset = function(d) {
    var offset = - d.height / 2; // for the center
    var focusedChild = this.curNode.getFocusedChild();

    // all tactic nodes are shifted such that the current tactic is centered
    assert(isGoal(this.curNode), "yOffset assumes the current node is a goal!");
    if (this.isCurGoalChild(d)) {
        assert(focusedChild !== undefined);
        return offset + (nodeY(d.parent) - nodeY(focusedChild)) * this.yFactor;
    }

    // all goal grandchildren are shifted such that the context line of the
    // current goal and the current suboal align
    if (this.isCurGoalGrandChild(d)) {
        return offset + this.descendantsOffset;
    }

    // the other nodes (current goal and its ancestors) stay where they need
    return offset;
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

ProofTree.prototype.getFocus = function() {
    $(":focus").blur();
}

ProofTree.prototype.newAlreadyStartedTheorem = function(lastResponse, tactics) {

    var self = this;

    this.tactics = tactics;

    // hide previous proof result if any, show svg if hidden
    this.svg.style("display", "");

    // will be reset in hInit callback, prevents stale uses
    this.rootNode = undefined;

    var success = false;

    self.hInit(lastResponse);

    //this.getFocus();
    //this.svg.on("click")();

}

function getTacticFromTacticish(d) {
    if (isTactic(d)) {
        return d;
    } else if (isTacticGroup(d)) {
        return d.getFocusedTactic();
    } else {
        throw d;
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

function getResponseFocused(response) {
    return response.rGoals.focused;
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
    var groupToAttachTo = this.curNode.getUserTacticsGroup();
    return asyncQueryAndUndo(t)
        .then(function(response) {
            if (isGood(response)) {
                var newChild = new TacticNode(
                    self,
                    groupToAttachTo,
                    t,
                    response
                );
                groupToAttachTo.tactics.unshift(newChild);
                groupToAttachTo.tacticIndex = 0;
                self.update();
                self.click(groupToAttachTo);
            } else {
                // TODO: not use alert
                alert(response.rResponse.contents);
            }
        })
        .catch(outputError);
}

/*
 * @return <Promise>
 */
ProofTree.prototype.runTactic = function(t, groupToAttachTo) {

    var self = this;

    var parentGoal = getClosestGoal(groupToAttachTo);
    var parentGoalRepr = goalNodeUnicityRepr(parentGoal);

    // if we correctly stored the last response in [parentGoal], we don't need
    // to query for status at this moment
    var beforeResponse = parentGoal.response;

    $("#loading-text").text(nbsp + nbsp + "Trying " + t);

    return asyncQueryAndUndo(t)
        .then(delayPromise(0))
        .then(function(response) {
            if (isGood(response)) {

                var unfocusedBefore = getResponseUnfocused(beforeResponse);
                var unfocusedAfter = getResponseUnfocused(response);
                var newChild = new TacticNode(
                    self,
                    groupToAttachTo,
                    t,
                    response
                );

                // only attach the newChild if it produces something
                // unique from existing children
                var newChildRepr = tacticNodeUnicityRepr(newChild);

                var resultAlreadyExists =
                    _(parentGoal.getTactics()).some(function(t) {
                        return t.tactic === newChild.tactic;
                        //return (tacticNodeUnicityRepr(t) === newChildRepr);
                    })
                ;

                var tacticIsUseless =
                    (newChild.goals.length === 1)
                    && (goalNodeUnicityRepr(newChild.goals[0])
                        === parentGoalRepr)
                ;

                if (!resultAlreadyExists && !tacticIsUseless) {
                    groupToAttachTo.addTactic(newChild);
                    self.update();
                }

            } else {

                //console.log("Bad response for", t, response);

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

    if (focusedOnEditor) { return; }

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

    // TODO: there should be no tactics!

    var groups = tacticsAndGroups.groups;

    var groupSparks = _(groups)
        .map(function(group) {
            var groupNode = self.findOrCreateGroup(curNode, group.name);
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
    this.tacticsWorklist = groupSparks;

    //console.log("REPOPULATING TACTICS WORKLIST", this.tacticsWorklist);

    this.processTactics();

}

ProofTree.prototype.findOrCreateGroup = function(goalNode, groupName) {
    var found = _(goalNode.tacticGroups)
        .find(function(tacticGroup) {
            return tacticGroup.name === groupName;
        })
    ;
    if (found !== undefined) { return found; }
    // else, create it
    var groupNode = new TacticGroupNode(this, goalNode, groupName);
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

    // There should only be one goal at that point
    this.rootNode = new GoalNode(this, undefined, response, 0);

    // doesn't matter much when this is done, so no chaining
    asyncStatus()
        .then(function(status) {
            self.rootNode.label = status.label;
        })
    ;

    this.curNode = this.rootNode;

    // this is now done later once 'Proof.' has been processed
    //this.refreshTactics();

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
    /*
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
    */
    // if the user uses his keyboard, highlight the focused path
    if (isGoal(this.curNode)) {
        var focusedChild = this.curNode.getFocusedChild();
        if (focusedChild === undefined) { return thin; }
        if (this.isCurNode(src) && focusedChild.id === tgt.id) { return thick; }
        // we want to thicken the path to the focused subgoal
        var focusedGrandChild = focusedChild.getFocusedChild();
        if (focusedGrandChild === undefined) { return thin; }
        if (focusedChild.id == src.id && focusedGrandChild.id === tgt.id) {
            return thick;
        }
        return thin;
    } else if (isTacticish(this.curNode)) {
        var focusedChild = this.curNode.getFocusedChild();
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
    d.width = d.nodeWidth();
    d.height = Math.ceil(rect.height);
}

function makeContextDivider() {
    return $("<hr>")
    // inlining the CSS for svg_datatourl
        .css("border", 0)
        .css("border-top", "1px solid black")
        .css("margin", 0)
    ;
}

function makeGoalNodePre() {
    return $("<pre>")
        .addClass("goalNode")
    // inlining some CSS for svg_datatourl
        .css("font-family", "monospace")
        .css("font-size", "14px")
        .css("line-height", "normal")
        .css("margin", 0)
        .css("padding", 0)
    ;
}

ProofTree.prototype.update = function() {

    if (focusedOnEditor) { return Promise.resolve(); }

    editorOnUpdate(this);

    var self = this;

    return new Promise(function (onFulfilled, onRejected) {

        // shorter name, expected to stay constant throughout
        var curNode = self.curNode;

        assert(isGoal(curNode));

        // if the viewpoint has been zoomed, cancel the zoom so that the computed
        // sizes are correct
        self.resetSVGTransform();

        var nodes = self.tree.nodes(self.rootNode);
        // now get rid of the fake nodes used for layout
        _(nodes)
            .each(function(node) {
                if (isTacticish(node) && node.getViewChildren().length === 0) {
                    node.children = [];
                }
            });
        nodes = _(nodes)
            .filter(function(node) { return node.type !== 'fake'; })
            .value()
        ;
        var links = self.tree.links(nodes);

        // we build the foreignObject first, as its dimensions will guide the others
        var textSelection = self.textLayer
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
            .style("margin", 0) // keep this line for svg_datatourl
            .style("padding", function(d) {
                return isGoal(d) ? goalBodyPadding + "px" : "0px 0px";
            })
            .style("background-color", "rgba(0, 0, 0, 0)")
        // should make it less painful on 800x600 videoprojector
        // TODO: fix computing diffs so that zooming is possible
            .style("font-size", (self.width < 1000) ? "12px" : "14px")
            .style("font-family", "monospace")
            .each(function(d) {
                var jqBody = $(d3.select(this).node());
                var jQContents;
                if (isTactic(d)) {
                    d.span = $("<div>")
                        .addClass("tacticNode")
                        .css("padding", "4px")
                        .css("text-align", "center")
                        .text(d.tactic);
                    jQContents = d.span;
                } else if (isTacticGroup(d)) {
                    return; // needs to be refreshed on every update, see below
                } else if (isGoal(d)) {
                    jQContents = makeGoalNodePre();
                    _(d.hyps).each(function(h) {
                        var jQDiv = $("<div>")
                            .html(PT.showHypothesis(h))
                            .attr("id", _.uniqueId())
                        ;
                        h.div = jQDiv[0];
                        jQContents.append(h.div);
                    });
                    jQContents.append(makeContextDivider());
                    d.goalSpan = $("<div>").html(showTerm(d.goalTerm));
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
                    d.span = $("<div>")
                        .addClass("tacticNode")
                        .css("padding", "4px")
                        .css("text-align", "center")
                    ;

                    // prepend a tactic node selector if necessary
                    if (nbTactics > 1) {

                        if (d.tacticIndex > 0) {
                            d.span.append(
                                $("<a>")
                                    .attr("href", "#")
                                    .text('◀')
                                    .click(function(e) {
                                        e.stopImmediatePropagation();
                                        d.shiftPrevInGroup();
                                    })
                            );
                        } else {
                            d.span.append(nbsp);
                        }

                        d.span.append(
                            '[' + (d.tacticIndex + 1) + '/' + d.tactics.length + ']'
                        );

                        if (d.tacticIndex < d.tactics.length - 1) {
                            d.span.append(
                                $("<a>")
                                    .attr("href", "#")
                                    .text('▶')
                                    .click(function(e) {
                                        e.stopImmediatePropagation();
                                        d.shiftNextInGroup();
                                    })
                            );
                        } else {
                            d.span.append(nbsp);
                        }

                        d.span.append($("<br>"));

                    }

                    d.span.append(
                        focusedTactic.tactic
                    );

                    jQContents = d.span;
                    jqBody.empty();
                    jqBody.append(jQContents);
                } else if (isGoal(d)) {
                    jQContents = makeGoalNodePre();
                    _(d.hyps).each(function(h) {
                        var jQDiv = $("<div>")
                            .html(PT.showHypothesis(h))
                            .attr("id", _.uniqueId())
                        ;
                        h.div = jQDiv[0];
                        jQContents.append(h.div);
                    });

                    jQContents.append(makeContextDivider());
                    d.goalSpan = $("<div>").html(showTerm(d.goalTerm));
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

        var curGoal = self.curGoal();
        var visibleChildren = _(curGoal.getViewChildren());
        var visibleGrandChildren = _(curGoal.getViewGrandChildren());
        var visibleNodes = _([]);
        if (hasParent(curGoal)) {
            visibleNodes = visibleNodes.concat([curGoal.parent]);
        }
        visibleNodes = visibleNodes.concat([curGoal]);
        visibleNodes = visibleNodes.concat(visibleChildren.value());
        visibleNodes = visibleNodes.concat(visibleGrandChildren.value());

        // xFactor is now fixed, so that the user experience is more stable
        if (self.rootNode.children === undefined || self.rootNode.children.length === 0) {
            self.xFactor = self.width;
        } else {
            var xDistance = nodeX(self.rootNode.children[0]) - nodeX(self.rootNode);
            /* width = 4 * xDistance * xFactor */
            self.xFactor = self.width / (4 * xDistance);
        }

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
        if (isGoal(self.curNode) && hasParent(self.curNode)) {
            var curNodeSiblings = _(self.curNode.parent.getViewChildren());
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
        self.yFactor = _.isEmpty(yFactors) ? self.height : _.max(yFactors);

        /*
          here we are looking for the descendant which should align with the current
          node. it used to be at the top of the view, now it's centered.
        */
        var centeredDescendant = undefined;
        if (isGoal(self.curNode)) {
            var centeredTactic = self.curNode.getFocusedChild();
            if (centeredTactic !== undefined) {
                centeredDescendant = centeredTactic.getFocusedChild();
                if (centeredDescendant === undefined) {
                    centeredDescendant = centeredTactic;
                }
            }
        }  else if (isTacticish(self.curNode)) {
            var t = getTacticFromTacticish(self.curNode);
            if (t.goals.length > 0) {
                centeredDescendant = t.goals[t.goalIndex];
            }
        } else {
            throw self.curNode;
        }

        if (centeredDescendant !== undefined) {
            if (isGoal(self.curNode) && isGoal(centeredDescendant)) {
                // computing the difference in height between the <hr> is not
                // obvious...
                var hrDelta =
                    self.curNode.goalSpan[0].offsetTop
                    - centeredDescendant.goalSpan[0].offsetTop
                ;
                self.descendantsOffset =
                    self.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
                    - (curGoal.height - centeredDescendant.height) / 2
                    + hrDelta
                ;
            } else if (isTacticish(self.curNode)) {
                var hrDelta =
                    self.curNode.parent.goalSpan[0].offsetTop
                    - centeredDescendant.goalSpan[0].offsetTop
                ;
                self.descendantsOffset =
                    self.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
                    - (curGoal.height - centeredDescendant.height) / 2
                    + hrDelta
                ;
            } else {
                self.descendantsOffset =
                    self.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
                ;
            }
        } else {
            self.descendantsOffset = 0;
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
                    // the root needs to spawn somewhere arbitrary: (0, 0.5)
                    d.cX0 = self.xOffset(d);
                    d.cY0 = 0.5 * self.yFactor + self.yOffset(d);
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
                    .on("click", function(d) {

                        asyncLog("CLICK " + nodeString(d));

                        d.click();

                    })
                ;
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

        var rectSelection = self.rectLayer.selectAll("rect").data(nodes, byNodeId);

        rectSelection.enter()
            .append("rect")
            .classed("goal", isGoal)
            .style("fill", function(d) {
                if (isGoal(d)) { return "#AEC6CF"; }
                if (isTacticish(d)) { return "#CB99C9"; }
                return "#000000";
            })
            .classed("tactic", isTacticish)
            .attr("width", function(d) { return d.width; })
            .attr("height", function(d) { return d.height; })
            .attr("x", function(d) { return d.cX0; })
            .attr("y", function(d) { return d.cY0; })
            .attr("rx", function(d) { return isGoal(d) ? 0 : 10; })
        ;

        rectSelection
            .classed("current", function(d) { return self.isCurNode(d); })
            .style("stroke", function(d) {
                return self.isCurNode(d) ? "#03C03C" : "";
            })
            .style("stroke-width", function(d) {
                return self.isCurNode(d) ? "4px" : "";
            })
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

        var linkSelection = self.linkLayer.selectAll("path").data(links, byLinkId);

        linkSelection.enter()
            .append("path")
            .classed("link", true)
            .attr("d", function(d) {
                var src = swapXY(centerRight0(d.source));
                var tgt = swapXY(centerLeft0(d.target));
                return self.diagonal({"source": src, "target": tgt});
            })
        // initial stroke is blue for goals that don't finish
            .attr("stroke", function(d) {
                if (isTacticGroup(d.target)
                    && d.target.getFocusedTactic().goals.length === 0) {
                    return "#00FF00";
                } else {
                    return "blue";
                }
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
            .attr("stroke", function(d) {
                if (isTacticGroup(d.target)
                    && d.target.getFocusedTactic().goals.length === 0) {
                    return "#00FF00";
                } else {
                    if ((isTacticGroup(d.source)
                         && d.source.getFocusedTactic().visited)
                        ||
                        (isTacticGroup(d.target)
                         && d.target.getFocusedTactic().visited)) {
                        return "purple";
                    } else {
                        return "blue";
                    }
                }
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

        var focusedGoal = self.getFocusedGoal();
        var diffData = (focusedGoal === undefined) ? [] : [focusedGoal];
        var diffSelection = self.diffLayer.selectAll("g.node-diff").data(
            diffData,
            byNodeId
        );

        diffSelection.enter()
            .append("g")
            .classed("node-diff", true)
            .classed("diff", true)
            .each(function(d) {
                // create these so that the field exists on first access
                d.addedSelections = [];
                d.removedSelections = [];
                // force the proper order of display, diffs on top of streams
                d.pathsGroup = d3.select(this).append("g").classed("paths", true); // streams
                d.rectsGroup = d3.select(this).append("g").classed("rects", true); // diffs
            })
                .style("opacity", 0)
            .transition()
            .duration(animationDuration)
            .style("opacity", 1)
        ;

        diffSelection
        // need to redo this every time now that nodes can change :(
            .each(function(d) {
                var gp = d.parent.parent;

                var d3this = d3.select(this);

                // adding diffs for the goal

                var subdiff = spotTheDifferences(gp.goalSpan, d.goalSpan);

                // there should be a goal stream whenever there are diffs
                var goalStreamData = subdiff.removed.length > 0 ? [undefined] : [];
                var goalStreamSelection =
                    d.pathsGroup.selectAll("path.goalstream")
                    .data(goalStreamData)
                ;

                goalStreamSelection.enter()
                    .append("path")
                    .classed("goalstream", true)
                    .attr("fill", diffBlue)
                    .attr("opacity", diffOpacity)
                    .attr("stroke-width", 0)
                    .attr(
                        "d",
                        connectRects(
                            elmtRect0(gp, gp.goalSpan[0]),
                            elmtRect0(d, d.goalSpan[0]),
                            undefined //d.parent.cX + d.parent.width/2
                        )
                    )
                ;

                goalStreamSelection
                    .transition()
                    .duration(animationDuration)
                    .attr(
                        "d",
                        connectRects(
                            elmtRect(gp, gp.goalSpan[0]),
                            elmtRect(d, d.goalSpan[0]),
                            undefined //d.parent.cX + d.parent.width/2
                        )
                    )
                ;

                goalStreamSelection.exit()
                    .remove()
                ;

                // var goalRemovedSelection =
                //     d.rectsGroup.selectAll("rect.goalremoved")
                //     .data(subdiff.removed)
                // ;

                // goalRemovedSelection.enter()
                //     .append("rect")
                //     .classed("goalremoved", true)
                //     .attr("fill", function(d, ndx) {
                //         return colorScale(ndx);
                //     })
                //     .attr("opacity", diffOpacity)
                // ;

                // goalRemovedSelection
                //     .each(function(jSpan) {
                //         var rect0 = elmtRect0(gp, jSpan[0]);
                //         var rect = elmtRect(gp, jSpan[0]);
                //         d3.select(this)
                //             .attr("width", rect.width)
                //             .attr("height", rect.height)
                //             .attr("x", rect0.left)
                //             .attr("y", rect0.top)
                //             .transition()
                //             .duration(animationDuration)
                //             .attr("x", rect.left)
                //             .attr("y", rect.top)
                //         ;
                //     })
                //         ;

                // var goalAddedSelection =
                //     d.rectsGroup.selectAll("rect.goaladded")
                //     .data(subdiff.added)
                // ;

                // goalAddedSelection.enter()
                //     .append("rect")
                //     .classed("goaladded", true)
                //     .attr("fill", function(d, ndx) {
                //         return colorScale(ndx);
                //     })
                //     .attr("opacity", diffOpacity)
                // ;

                // goalAddedSelection
                //     .each(function(jSpan) {
                //         var rect0 = elmtRect0(d, jSpan[0]);
                //         var rect = elmtRect(d, jSpan[0]);
                //         d3.select(this)
                //             .attr("width", rect.width)
                //             .attr("height", rect.height)
                //             .attr("x", rect0.left)
                //             .attr("y", rect0.top)
                //             .transition()
                //             .duration(animationDuration)
                //             .attr("x", rect.left)
                //             .attr("y", rect.top)
                //         ;
                //     })
                //         ;

                // adding diffs for the hypotheses
                var diffList = computeDiffList(gp.hyps, d.hyps);

                d.diffListSelection =
                    d.pathsGroup.selectAll("g.diff-item")
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
                                .attr("stroke-width", 0)
                            ;

                        } else if (diff.newHyp === undefined) {

                            var oldHyp = diff.oldHyp;
                            d3this
                                .append("path")
                                .attr("fill", diffRed)
                                .attr("opacity", diffOpacity)
                                .attr("stroke-width", 0)
                            ;

                        } else {

                            var oldHyp = diff.oldHyp;
                            var newHyp = diff.newHyp;
                            if (JSON.stringify(oldHyp.hType)
                                !== JSON.stringify(newHyp.hType)) {
                                d3this
                                    .insert("path", ":first-child")
                                    .attr("fill", diffBlue)
                                    .attr("opacity", diffOpacity)
                                    .attr("stroke-width", 0)
                                ;

                            }

                        }
                    })
                        ;

                // keep track of how far we are vertically to draw the diffs with
                // only one side nicely
                var leftY0 = gp.cY0 + goalBodyPadding;
                var rightY0 = d.cY0 + goalBodyPadding;
                var leftY = gp.cY + goalBodyPadding;
                var rightY = d.cY + goalBodyPadding;

                d.diffListSelection
                    .each(function(diff) {

                        if (diff.oldHyp === undefined) {
                            var newHyp = diff.newHyp;
                            d3.select(this).select("path")
                                .attr(
                                    "d",
                                    connectRects(
                                        emptyRect0(gp, leftY0),
                                        elmtRect0(d, newHyp.div),
                                        undefined //d.parent.cX + d.parent.width/2
                                    )
                                )
                                .transition()
                                .duration(animationDuration)
                                .attr(
                                    "d",
                                    connectRects(
                                        emptyRect(gp, leftY),
                                        elmtRect(d, newHyp.div),
                                        undefined //d.parent.cX + d.parent.width/2
                                    )
                                )
                            ;
                            rightY0 = elmtRect0(d, newHyp.div).bottom;
                            rightY = elmtRect(d, newHyp.div).bottom;

                        } else if (diff.newHyp === undefined) {

                            var oldHyp = diff.oldHyp;
                            d3.select(this).select("path")
                                .attr(
                                    "d",
                                    connectRects(
                                        elmtRect0(gp, oldHyp.div),
                                        emptyRect0(d, rightY0),
                                        undefined //d.parent.cX + d.parent.width/2
                                    )
                                )
                                .transition()
                                .duration(animationDuration)
                                .attr(
                                    "d",
                                    connectRects(
                                        elmtRect(gp, oldHyp.div),
                                        emptyRect(d, rightY),
                                        undefined //d.parent.cX + d.parent.width/2
                                    )
                                )
                            ;
                            leftY0 = elmtRect0(gp, oldHyp.div).bottom;
                            leftY = elmtRect(gp, oldHyp.div).bottom;

                        } else {

                            var oldHyp = diff.oldHyp;
                            var newHyp = diff.newHyp;
                            if (JSON.stringify(oldHyp.hType) !== JSON.stringify(newHyp.hType)) {

                                d3.select(this).select("path")
                                    .attr(
                                        "d",
                                        connectRects(
                                            elmtRect0(gp, oldHyp.div),
                                            elmtRect0(d, newHyp.div),
                                            undefined //d.parent.cX + d.parent.width/2
                                        )
                                    )
                                    .transition()
                                    .duration(animationDuration)
                                    .attr(
                                        "d",
                                        connectRects(
                                            elmtRect(gp, oldHyp.div),
                                            elmtRect(d, newHyp.div),
                                            undefined //d.parent.cX + d.parent.width/2
                                        )
                                    )
                                ;

                                var subdiff = spotTheDifferences(
                                    oldHyp.div,
                                    newHyp.div
                                );

                                // var diffId = byDiffId(diff);
                                // d.removedSelections[diffId] =
                                //     d.rectsGroup.selectAll("rect.removed")
                                //     .data(subdiff.removed)
                                // ;

                                // d.removedSelections[diffId].enter()
                                //     .append("rect")
                                //     .classed("removed", true)
                                //     .attr("fill", function(d, ndx) {
                                //         return colorScale(ndx);
                                //     })
                                //     .attr("opacity", diffOpacity)
                                // ;

                                // d.removedSelections[diffId].exit()
                                //     .remove()
                                // ;

                                // d.addedSelections[diffId] =
                                //     d.rectsGroup.selectAll("rect.added")
                                //     .data(subdiff.added)
                                // ;

                                // d.addedSelections[diffId].enter()
                                //     .append("rect")
                                //     .classed("added", true)
                                //     .attr("fill", function(d, ndx) {
                                //         return colorScale(ndx);
                                //     })
                                //     .attr("opacity", diffOpacity)
                                // ;

                                // d.addedSelections[diffId].exit()
                                //     .remove()
                                // ;

                                // // TODO: there is a bug here where this does not get
                                // // refreshed properly when nodes show up. To
                                // // reproduce, load bigtheorem.v, run intros, and
                                // // move down one tactic quickly.
                                // //console.log(diff, byDiffId(diff));
                                // var diffId = byDiffId(diff);

                                // d.removedSelections[diffId]
                                //     .each(function(jSpan) {
                                //         var rect0 = elmtRect0(gp, jSpan[0]);
                                //         var rect = elmtRect(gp, jSpan[0]);
                                //         d3.select(this)
                                //             .attr("width", rect.width)
                                //             .attr("height", rect.height)
                                //             .attr("x", rect0.left)
                                //             .attr("y", rect0.top)
                                //             .transition()
                                //             .duration(animationDuration)
                                //             .attr("x", rect.left)
                                //             .attr("y", rect.top)
                                //         ;
                                //     })
                                //         ;

                                // d.addedSelections[diffId]
                                //     .each(function(jSpan) {
                                //         var rect0 = elmtRect0(d, jSpan[0]);
                                //         var rect = elmtRect(d, jSpan[0]);
                                //         d3.select(this)
                                //             .attr("width", rect.width)
                                //             .attr("height", rect.height)
                                //             .attr("x", rect0.left)
                                //             .attr("y", rect0.top)
                                //             .transition()
                                //             .duration(animationDuration)
                                //             .attr("x", rect.left)
                                //             .attr("y", rect.top)
                                //         ;
                                //     })
                                //         ;

                            }

                            leftY0 = elmtRect0(gp, oldHyp.div).bottom;
                            leftY = elmtRect(gp, oldHyp.div).bottom;

                            /*
                              we don't want to move the right cursor if the
                              right hypothesis was not the very next
                              hypothesis. this happens when a hypothesis gets
                              moved down the list of hypotheses.
                             */

                            if (!diff.isJump) {
                                rightY0 = elmtRect0(d, newHyp.div).bottom;
                                rightY = elmtRect(d, newHyp.div).bottom;
                            }

                        }

                    })
                        ;

                d.diffListSelection.exit()
                    .remove()
                ;

            });

        diffSelection.exit()
            .remove()
        ;

        // refocus the viewport

        self.viewportX = - (
            hasParent(curNode)
                ? curNode.parent.cX
                : curNode.cX // TODO: could do some math to align it the same way
        );

        self.viewportY =
            - (
                isGoal(curNode)
                    ? (curNode.cY + curNode.height / 2 - self.height / 2)
                    : (curNode.parent.cY + curNode.parent.height / 2 - self.height / 2)
            )
        ;

        self.viewport
            .transition()
            .duration(animationDuration)
            .attr("transform",
                  "translate(" + self.viewportX + ", " + self.viewportY + ")"
                 )
        ;

        /*
          It is important to update cX0 for all nodes so that we can uniformly
          initialize links to start between their source's cX0 and their
          target's cX0.  Without this, links created from nodes that have moved
          away from their cX0 will seem to appear from the node's old position
          rather than its current one.
        */
        _(nodes).each(function(d) {
            d.x0 = d.x;
            d.y0 = d.y;
            d.cX0 = d.cX;
            d.cY0 = d.cY;
        });

        //this.updateDebug();

        onFulfilled();

    });

}

function byDiffId(d) {
    var res = "{";
    if (d.oldHyp !== undefined) { res += d.oldHyp.hName; }
    res += "-";
    if (d.newHyp !== undefined) { res += d.newHyp.hName; }
    return res + "}";
}

function sameNameAs(a) {
    return function(b) { return a.hName === b.hName; };
}

function computeDiffList(oldHypsOriginal, newHypsOriginal) {
    var diffList = [];

    // slice() creates a shallow copy, since we will mutate this
    var oldHyps = oldHypsOriginal.slice();
    var newHyps = newHypsOriginal.slice();

    while (oldHyps.length > 0 && newHyps.length > 0) {
        var oldHyp = oldHyps[0];
        var newHyp = newHyps[0];
        // either the first two match
        if (oldHyp.hName === newHyp.hName) {
            diffList.push({"oldHyp": oldHyp, "newHyp": newHyp, "isJump": false});
            oldHyps.shift();
            newHyps.shift();
            continue;
        }
        var matchesOld = _(newHyps).find(sameNameAs(oldHyp));
        // or the first old has disappeared
        if (matchesOld === undefined) {
            diffList.push({"oldHyp": oldHyp, "newHyp": undefined, "isJump": false});
            oldHyps.shift();
            continue;
        }
        // or the first old has moved, but the first new has appeared
        var matchesNew = _(oldHyps).find(sameNameAs(newHyp));
        if (matchesNew === undefined) {
            diffList.push({"oldHyp": undefined, "newHyp": newHyp, "isJump": false});
            newHyps.shift();
            continue;
        }
        // otherwise, register matchesOld as a "jump"
        diffList.push({"oldHyp": oldHyp, "newHyp": matchesOld, "isJump": true});
        oldHyps.shift();
        _(newHyps).remove(sameNameAs(matchesOld));
    }

  // now register the remaining disappearing
    _(oldHyps).each(function(oldHyp) {
        diffList.push({"oldHyp": oldHyp, "newHyp": undefined, "isJump": false});
    });

    // now register the remaining appearing
    _(newHyps).each(function(newHyp) {
        diffList.push({"oldHyp": undefined, "newHyp": newHyp, "isJump": false});
    });

    return diffList;
}

/*
 * Returns a rect of the absolute position of [elmt] within the canvas. It needs
 * [node] in order to return absolute values, where [node] is the node element
 * within which [elmt] lives.
 */
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

function elmtRect0(node, elmt) {
    var rect = elmt.getBoundingClientRect();
    var containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect();
    var left = node.cX0 + deltaX(containerRect, rect);
    var top = node.cY0 + deltaY(containerRect, rect);
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
            asyncLog("UPGROUP " + nodeString(n.getViewChildren()[n.tacticIndex]));
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
    var viewChildren = n.getViewChildren();
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
        this.shiftPrevGoal(n.getFocusedTactic());
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
        this.shiftNextGoal(n.getFocusedTactic());
    } else {
        throw n;
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
function isGoal(node) {
    if (node === undefined) {
        throw ['isGoal', node];
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

    var children = curNode.getViewChildren();

    this.usingKeyboard = true;

    //console.log(d3.event.keyCode);

    switch (d3.event.keyCode) {

    case 37: // Left
    //case 65: // a
        d3.event.preventDefault();
        if (hasParent(curNode)) {
            asyncLog("LEFT " + nodeString(curNode.parent));
            curNode.parent.click();
        } else {
            // when at the root node, undo the last action (usually Proof.)
            onCtrlUp(false);
        }
        break;

    case 39: // Right
    //case 68: // d
        d3.event.preventDefault();
        var dest = curNode.getFocusedChild();
        if (dest === undefined) { break; }
        asyncLog("RIGHT " + nodeString(dest));
        dest.click();
        break;

    case 38: // Up
    //case 87: // w
        d3.event.preventDefault();
        if (d3.event.shiftKey) {
            if (isGoal(curNode)) {
                this.shiftPrevGoal(curNode.getFocusedChild());
            } else if (isTacticish(curNode)) { // do the same as without Shift
                this.shiftPrevGoal(curNode);
            } else {
                throw ['keydownHandler', curNode];
            }
        } else {
            if (isGoal(curNode)) {
                this.shiftPrevByTacticGroup(curNode);
            } else if (isTacticish(curNode)) {
                this.shiftPrevGoal(curNode);
            } else {
                throw ['keydownHandler', curNode];
            }
        }
        break;

    case 40: // Down
    //case 83: // s
        d3.event.preventDefault();
        if (d3.event.shiftKey) {
            if (isGoal(curNode)) {
                this.shiftNextGoal(curNode.getFocusedChild());
            } else if (isTacticish(curNode)) { // do the same as without Shift
                this.shiftNextGoal(curNode);
            } else {
                throw ['keydownHandler', curNode];
            }
        } else {
            if (isGoal(curNode)) {
                this.shiftNextByTacticGroup(curNode);
            } else if (isTacticish(curNode)) {
                this.shiftNextGoal(curNode);
            } else {
                throw ['keydownHandler', curNode];
            }
        }
        break;

    case 219: // [
        var focusedChild = curNode.getFocusedChild();
        if (isTacticGroup(focusedChild)) {
            focusedChild.shiftPrevInGroup();
        }
        break;

    case 221: // ]
        var focusedChild = curNode.getFocusedChild();
        if (isTacticGroup(focusedChild)) {
            focusedChild.shiftNextInGroup();
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

function span(t) {
    return $("<span>")
        .css("vertical-align", "top")
        .html(t)
    ;
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
    this.displayThisProof(this.rootNode.getProof());
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
        return showNames(t[0]) + syntax(":") + ' ' + showTermAux(t[1], 0, 0, false);
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
                    + ' ' + syntax("::") + ' '
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
        break;

        case "OrPatterns":
        var c = p.contents;
        var patterns = c[0];
        return (
            syntax("(")
                + _(patterns).reduce(function(acc, orpattern, ndx) {
                    return (
                        (ndx > 0 ? syntax(",") : "")
                            + _(orpattern).reduce(function(acc, pattern, ndx) {
                                return (
                                    (ndx > 0 ? "|" : "")
                                        + showPatternAux(pattern, false)
                                );
                            })
                    );
                })
                + syntax(")")
        );
        break;

        default:
        alert("Unknown pattern: " + p.tag);

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
    return repeat(2 * depth, " ");
}

var precedence = 0;

var precMin    = precedence++;

// low precedence

var precEquiv  = precedence++;
var precArrow  = precedence++;
var precOr     = precedence++;
var precAnd    = precedence++;
var precEqual  = precedence++; var precNotEqual = precEqual;
var precAppend = precedence++;
var precCons   = precedence++;
var precOrB    = precedence++;
var precAndB   = precedence++;
var precPlus   = precedence++; var precMinus = precPlus;
var precMult   = precedence++;
var precForall = precedence++;
var precApp    = precedence++;

// high precedence

var precMax   = precedence++;

var nbsp = "&nbsp;";
function vernac(s) { return '<span class="vernac">' + s + '</span>'; }
function syntax(s) { return '<span class="syntax">' + s + '</span>'; }
function ident(s) { return '<span class="identifier">' + s + '</span>'; }
function term(s) { return '<span class="term">' + s + '</span>'; }

function showConstructor(t) {
    var name = t[0];
    if (t[1] === null) {
        return syntax("|")
            + ' '
            + ident(name)
        ;
    } else {
        var type = showTermInline(t[1]);
        return syntax("|")
            + ' '
            + ident(name)
            + ' '
            + syntax(":")
            + ' '
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
            + ' '
            + ident(name)
            + ' '
            + syntax(":")
            + ' '
            + type
            + ' '
            + syntax(":=")
            + "<br>"
            + _(constructors).reduce(function(acc, elt) { return acc + elt + "<br>"; }, "")
            + syntax(".")
        ;

    case "Theorem":
        var name = c[0];
        var type = showTermInline(c[1]);
        return vernac("Theorem")
            + ' '
            + ident(name)
            + ' '
            + syntax(":")
            + ' '
            + type
            + syntax(".")
        ;

    case "Definition":
        var name = c[0];
        var args = _(c[1]).map(showBinder);
        var type = (c[2] !== null)
            ? syntax(":") + ' ' + showTermInline(c[2]) + ' '
            : "";
        var term = showTermIndent(c[3], 1);
        return vernac("Definition")
            + ' '
            + ident(name)
            + ' '
            + _(args).reduce(function(acc, elt) {
                return acc + syntax("(") + elt + syntax(")") + ' '; }, "")
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
            ? syntax(":") + ' ' + showTermInline(c[3]) + ' '
            : "";
        var term = showTermIndent(c[4], 1);
        return vernac("Fixpoint")
            + ' '
            + ident(name)
            + ' '
            + _(args).reduce(function(acc, elt) {
                return acc + syntax("(") + elt + syntax(")") + ' '; }, "")
            + (
                (decreasing !== null)
                    ? syntax("{") + ' ' + syntax("struct")
                    + ' ' + decreasing + ' ' + syntax("}") + ' '
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
    return _(items).reduce(function(acc, item, ndx) {
        var term = item[0];
        var matchAs = item[1];
        var matchIn = item[2];
        return (
            acc
                + (ndx > 0 ? syntax(",") + ' ' : "")
                + showTermInline(term)
                + (matchAs ? ' ' + syntax("as") + ' ' + matchAs : "")
                + (matchIn ? ' ' + syntax("in") + ' ' + showTermInline(matchIn) : "")
        );
    }, "");
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
            syntax("forall") + showBinders(c[0]) + syntax(",")
                + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
                + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Lambda":
        return par(
            precMin,
            syntax("fun") + showBinders(c[0]) + ' ' + syntax("=>")
                + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
                + showTermAux(c[1], indentation + 1, precMin, newline)
        );

    case "Exists":
        return par(
            precForall,
            syntax("exists") + showBinders(c[0]) + syntax(",")
                + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
                + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Arrow":
        return term(
            showTermAux(c[0], indentation, precArrow, false)
                + ' ' + syntax("->")
                + (newline ? "<br/>" + indent : " ")
                + showTermAux(c[1], indentation, precParent, newline)
        );

    case "Match":
        var matchItems = c[0];
        var maybeType = c[1];
        var equations = c[2];
        return term(
            syntax("match") + ' '
                + showMatchItems(matchItems) + ' '
                + (maybeType
                   ? syntax(":") + ' ' + showTermAux(c[1], 0, precMin, false)
                   : ""
                  )
                + syntax("with") + "<br>"
                + _(equations).reduce(function(acc, elt) {
                    var patterns = showPatterns(elt[0]);
                    var body = showTermAux(elt[1], indentation + 1, precParent, newline);
                    return acc
                        + getIndent(indentation) + syntax("|") + ' '
                        + patterns
                        + ' '
                        + syntax("=>")
                        + (
                            (body.indexOf("<br>") === -1)
                                ? ' ' + body
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
                return showOp(c, "/\\", precAnd);

            case "or":
                return showOp(c, "\\/", precOr);

            case "andb":
                return showOp(c, "&&", precAndB);

            case "orb":
                return showOp(c, "||", precOrB);

            case "iff":
                return showOp(c, "<->", precEquiv);

            // case "cons":
            //     return showOp(c, "::", precCons);

            // case "app":
            //     return showOp(c, "++", precAppend);

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

function inlineBlock(contents) {
    return '<div style="display: inline-block; max-width: 100%; vertical-align: top;">' + contents + '</div>';
}

function showHypothesis(h) {
    var res = h.hName;
    if (h.hValue !== null) {
        res = res + ' ' + syntax(":=") + ' ' + showTermInline(h.hValue);
    }
    res = inlineBlock(res + ' ' + syntax(":") + ' ')
        + inlineBlock(showTermInline(h.hType));
    return res;
}
PT.showHypothesis = showHypothesis;

function showHypothesisText(h) {
    var res = h.hName;
    if (h.hValue !== null) {
        res = res + " := " + showTermText(h.hValue);
    }
    res = res + " : " + showTermText(h.hType);
    return res;
}
PT.showHypothesisText = showHypothesisText;

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
    if (isGoal(d)) {
        return JSON.stringify(
            {
                "id": d.id,
                "name": d.name,
                "depth": d.depth,
                "hyps": _(d.hyps).map(function(h) {
                    return {
                        "hName": h.hName,
                        "hType": h.hType,
                        "hValue": h.hValue,
                    };
                }).value(),
            }
        );
    } else if (isTactic(d)) {
        return JSON.stringify(
            {
                "id": d.id,
                "tactic": d.tactic,
                "depth": d.depth,
            }
        );
    } else if (isTacticGroup(d)) {
        return JSON.stringify(
            {
                "id": d.id,
                "depth": d.depth,
                "name": d.name,
            }
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
    console.log(error, error.stack);
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

/*
 * Constructs a [Node] object. We preemptively fill the [parent] and [depth]
 * fields because D3 will only fill them for the visible nodes of the tree,
 * while some algorithms require it before a node has ever been visible.
*/
function Node(proofTree, parent) {
    this.id = _.uniqueId();
    this.proofTree = proofTree;
    this.parent = parent;
    this.depth = (parent === undefined) ? 0 : parent.depth + 1;
    this.solved = false;
}

Node.prototype.isSolved = function() { return this.solved; }
Node.prototype.hasParent = function() { return this.parent !== undefined; }

GoalNode.prototype.isCurNode = function() {
    return this.id === this.proofTree.curNode.id;
}

Node.prototype.isCurNodeAncestor = function() {
    var curNode = this.proofTree.curNode;
    var common = this.proofTree.commonAncestor(curNode, this);
    return this.id === common.id;
}

Node.prototype.isAncestorOf = function(node) {
    var common = this.proofTree.commonAncestor(node, this);
    return this.id === common.id;
}

Node.prototype.isCurNodeChild = function() {
    // this will do for now, TODO make these node methods
    return this.proofTree.isCurNodeChild(this);
}

Node.prototype.isCurNodeParent = function() {
    // this will do for now, TODO make these node methods
    return this.proofTree.isCurNodeParent(this);
}

/*
 * This implementation is generic as long as children implement
 * [getViewChildren].
 */
Node.prototype.getViewGrandChildren = function() {
    return (
        _(this.getViewChildren())
            .map(function(e) { return e.getViewChildren(); })
            .flatten(true)
            .value()
    );
}

var userTacticsGroupName = 'PeaCoq User Tactics';

/*
 * [proofTree] is the proof tree the node belongs to
 * [parentTactic] is a self-explanatory [TacticNode]
 * [response] ...
 * [index] should be the index of the goal within its tactic [rGoals]
 */
function GoalNode(proofTree, parentTactic, response, index) {
    var goal = response.rGoals.focused[index];
    Node.call(
        this,
        proofTree,
        (parentTactic === undefined) ? undefined : parentTactic.parent
    );
    var goalTerm = extractGoal(goal.gGoal);
    this.hyps = _(goal.gHyps).map(extractHypothesis).value();
    this.ndx = index + 1; // used in Focus, Coq uses 1-index
    this.gid = goal.gId;
    this.goalTerm = goalTerm;
    this.goalString = showTermText(goalTerm);
    this.tacticGroups = [
        new TacticGroupNode(proofTree, this, userTacticsGroupName)
    ];
    this.tacticIndex = 0;
    this.parentTactic = parentTactic;
    /*
     * This field will be populated every time this [GoalNode] is visited, and
     * will contain the response obtained upon last visiting it.
     */
    this.response = response;
    this.openBraces = 0;
    this.closedBraces = 0;

    // TO REMOVE
    this.type = 'goal';
}

GoalNode.prototype = Object.create(Node.prototype);
GoalNode.prototype.constructor = GoalNode;

/*
 * [proofTree] is the proof tree to which this node belongs
 * [parent] should be a [TacticGroupNode]
 * [tactic] is the name of the tactic
 * [response] is the response obtained after running the tactic
 */
function TacticNode(proofTree, parent, tactic, response) {
    var self = this;
    Node.call(this, proofTree, parent);
    this.tactic = tactic;
    this.visited = false;

    var focusedBefore = getResponseFocused(parent.parent.response);
    var focusedAfter = getResponseFocused(response);

    var unfocusedBefore = getResponseUnfocused(parent.parent.response);
    var unfocusedAfter = getResponseUnfocused(response);

    var remainingSubgoals;
    if (_.isEqual(unfocusedAfter, unfocusedBefore)) {
        if (focusedBefore.length > 1
            && focusedAfter[0].gId === focusedBefore[1].gId) {
            remainingSubgoals = [];
        } else {
            var focusDelta = focusedAfter.length - focusedBefore.length;
            remainingSubgoals = response.rGoals.focused.slice(0, focusDelta + 1);
        }
    } else {
        remainingSubgoals = [];
    }
    //console.log(tactic, focusDelta, parent.parent.response, response, remainingSubgoals);
    this.goals = _(remainingSubgoals).map(function(goal, index) {
        return new GoalNode(proofTree, self, response, index);
    }).value();
    this.goalIndex = 0;

    // TO REMOVE
    this.type = 'tactic';
    this.response = response;
}

TacticNode.prototype = Object.create(Node.prototype);
TacticNode.prototype.constructor = TacticNode;

TacticNode.prototype.refreshGoals = function() {
    var self = this;
    this.goals = _(this.originalGoals).map(function(goal, index) {
        return new GoalNode(self.proofTree, self, goal, index);
    }).value();
    this.goalIndex = 0;
}

function TacticGroupNode(proofTree, parent, name) {
    Node.call(this, proofTree, parent);
    this.name = name;
    this.tactics = [];
    this.tacticIndex = 0;

    // TO REMOVE
    this.type = 'tacticgroup';
}

TacticGroupNode.prototype = Object.create(Node.prototype);
TacticGroupNode.prototype.constructor = TacticGroupNode;

/* nodeWidth */

GoalNode.prototype.nodeWidth = function() {
    return this.proofTree.goalWidth;
}

TacticNode.prototype.nodeWidth = function() {
    return this.proofTree.tacticWidth;
}

TacticGroupNode.prototype.nodeWidth = function() {
    return this.proofTree.tacticWidth;
}

/*
 * [getFocusedTacticGroup] is self-explanatory. It may return undefined if all
 * groups are empty.
 */

GoalNode.prototype.getFocusedTacticGroup = function() {
    var nonEmptyTacticGroups = _(this.tacticGroups)
        .filter(function(group) { return (group.tactics.length > 0); })
        .value()
    ;
    if (nonEmptyTacticGroups.length === 0) { return []; }
    return nonEmptyTacticGroups[this.tacticIndex];
}

/*
 * [getViewChildren] returns the children of the considered node in the current
 * view.
 */

GoalNode.prototype.getViewChildren = function() {
    if (this.isSolved()) { return []; }
    var nonEmptyTacticGroups = _(this.tacticGroups)
        .filter(function(group) { return (group.tactics.length > 0); })
        .value()
    ;

    if (nonEmptyTacticGroups.length === 0) { return []; }
    if (this.proofTree.isCurNode(this)) {

        // WARNING: this code creates bugs because it alters the view in ways
        // the rest of the code was not robust to. For instance, if the user
        // has scrolled to the n-th tactic group, but suddenly a finisher
        // returns, this would remove non-finisher, and the cursor would be
        // out of bounds.

        /*
        // if any tactic group contains a finisher, only keep tactic groups
        // that contain a finisher

        // if there exists a solving node, filter out the non-solving nodes
        if (_(nonEmptyTacticGroups).some(function(group) {
            return _(group.tactics).some(function(tactic) {
                return tactic.goals.length === 0;
            });
        })) {
            nonEmptyTacticGroups = _(nonEmptyTacticGroups).filter(function(group) {
                return _(group.tactics).some(function(tactic) {
                    return tactic.goals.length === 0;
                });
            }).value();
        }
        */

        return nonEmptyTacticGroups;

    } else if (this.isCurNodeAncestor()) {
        /* If the node is collapsed, it needs to have one child if it is an
           ancestor of the current node, so that the current node is reachable. */
        return [nonEmptyTacticGroups[this.tacticIndex]];
    } else {
        return [];
    }
}

TacticNode.prototype.getViewChildren = function() {
    if (this.isSolved()) { return []; }
    if (this.goals.length === 0) { return []; }
    // Note: This SHOULD NOT be the current node!
    return this.goals;
}

TacticGroupNode.prototype.getViewChildren = function() {
    if (this.isSolved()) { return []; }
    if (this.tactics.length === 0) { return []; }
    var focusedTactic = this.tactics[this.tacticIndex];
    return focusedTactic.getViewChildren();
}

/*
 * [getFocusedChild] returns the child under focus within the view.
 * It always returns a [GoalNode] or a [TacticNode].
 */

GoalNode.prototype.getFocusedChild = function() {
    var viewChildren = this.getViewChildren();
    if (viewChildren.length === 0) { return undefined; }
    return viewChildren[this.tacticIndex];
}

TacticNode.prototype.getFocusedChild = function() {
    var viewChildren = this.getViewChildren();
    if (viewChildren.length === 0) { return undefined; }
    return viewChildren[this.goalIndex];
}

TacticGroupNode.prototype.getFocusedChild = function() {
    var viewChildren = this.getViewChildren();
    if (viewChildren.length === 0) { return undefined; }
    return viewChildren[this.tactics[this.tacticIndex].goalIndex];
}

/* makes [this] the focused child of its parent [TacticNode] */
GoalNode.prototype.makeFocused = function() {
    var self = this;
    var parentTactic = this.parentTactic;
    if (parentTactic === undefined) { return; }
    parentTactic.visited = true;
    parentTactic.goalIndex = _(parentTactic.goals)
        .findIndex(function(goal) { return goal.id === self.id; })
    ;
    assert(parentTactic.goalIndex !== -1);
}

TacticGroupNode.prototype.makeFocused = function() {
    var self = this;
    var parentGoal = this.parent;
    parentGoal.tacticIndex = _(parentGoal.tacticGroups)
        .filter(function(group) { return (group.tactics.length > 0); })
        .findIndex(function(node) { return node.id === self.id; })
    ;
    assert(parentGoal.tacticIndex !== -1);
}

TacticNode.prototype.makeFocused = function() {
    var self = this;
    var parentTacticGroup = this.parent;
    parentTacticGroup.tacticIndex = _(parentTacticGroup.tactics)
        .findIndex(function(tactic) { return tactic.id === self.id; })
    ;
    assert(parentTacticGroup.tacticIndex !== -1);
}

/*
GoalNode.prototype.makeFocused = function() {
    Node.prototype.makeFocused.call(this);
    if(this.hasParent() && this.parent.constructor === TacticGroupNode) {
        var parentTactic = this.parent.getFocusedTactic();
        parentTactic.setFocusedChild(this);
    }
}
*/

/*
 * [makeFocusedUptoGoal] makes [this] the focused goal of [this.parentTactic],
 * the latter the previous goal of its parent tactic group, and the latter the
 * focused tactic group of its parent goal.
 */

GoalNode.prototype.makeFocusedUptoGoal = function() {
    this.makeFocused();
    if (this.parentTactic !== undefined) {
        this.parentTactic.makeFocused();
        this.parentTactic.parent.makeFocused();
    }
}

TacticNode.prototype.makeFocusedUptoGroup = function() {
    this.makeFocused();
    this.parent.makeFocused();
}

/*
 * [getFocusedTactic] returns the focused TacticNode of a group.
 */

TacticGroupNode.prototype.getFocusedTactic = function() {
    if (this.tactics.length === 0) { return undefined; }
    return this.tactics[this.tacticIndex];
}

/*
 * [getTactics] returns all the tactic nodes under the node.
 */

GoalNode.prototype.getTactics = function() {
    return _(this.tacticGroups)
        .map(function(g) { return g.getTactics(); })
        .flatten(true)
        .value()
    ;
}

TacticGroupNode.prototype.getTactics = function() {
    return this.tactics;
}

/*
 * [getProof] builds the proof derivation from a solved node, as a nested array.
 */

GoalNode.prototype.getProof = function() {
    return _(this.getTactics()).find('solved').getProof();
}

TacticNode.prototype.getProof = function() {
    return [
        this.tactic,
        _(this.goals).map(function(g) { return g.getProof(); }).value(),
    ];
}

TacticGroupNode.prototype.getProof = function() {
    // assuming the solved tactic is focused
    return this.getFocusedTactic().getProof();
}

/*
 * [addTactic] adds [tacticNode] to a tactic group.
 */

TacticGroupNode.prototype.addTactic = function(tacticNode) {
    this.tactics.push(tacticNode);
}

/*
 * [resetWith] resets a goal node with an original goal response.
 */

GoalNode.prototype.resetWith = function(newGoal) {
    var goalTerm = extractGoal(newGoal.gGoal);
    this.hyps = _(newGoal.gHyps).map(extractHypothesis).value();
    this.gid = newGoal.gId;
    this.goalTerm = goalTerm;
    this.goalString = showTermText(goalTerm);
    this.tacticGroups =
        [new TacticGroupNode(this.proofTree, this, userTacticsGroupName)]
    ;
    this.tacticIndex = 0;
}

/*
 * [getUserTacticsGroup] returns the user tactics group of a [GoalNode].
 */

GoalNode.prototype.getUserTacticsGroup = function() {
    // for now, it should always be at position 0
    var userTacticsGroup = this.tacticGroups[0];
    if (userTacticsGroup.name !== userTacticsGroupName) {
        throw ['getUserTacticsGroup', this];
    }
    return userTacticsGroup;
}

ProofTree.prototype.onUndo = function(fromUser, undone, response) {
    var undone = coqTrim(undone);
    this.curNode.onUndo(fromUser, undone, response);
}

ProofTree.prototype.beforeToproveConsumption = function() {
    var toprove = getToprove();
    var nextIndex = next(toprove);
    var nextPieceProcessed = toprove.substring(0, nextIndex);
    switch (coqTrim(nextPieceProcessed)) {

    case '{':
    case '}':
        // these are fine to proceed
        break;

    default:
        // if a tactic is about to be pushed without focus, force it!
        // first case: there is nothing to be done and we are unfocused
        if (isTacticGroup(this.curNode)) {
            //if (autoLayout) { safePrependToprove('{'); }
        }
        break;

    }
}

ProofTree.prototype.onResponse = function(queryType, query, response) {
    var self = this;
    switch (queryType) {
    case 'query':
        //console.log("response", response.toString());
        // if a query succeeded, we don't want to keep refreshing tactics
        this.tacticsWorklist = [];
        switch (response.rResponse.tag) {
        case 'Good':
            this.curNode.reactTo(coqTrim(query), response);
            break;
        case 'Fail':
            console.log('Query failed', query, response);
            break;
        }
    }
}

function isUpperCase(character) {
    return /^[A-Z]$/.test(character);
}

function isLowerCase(character) {
    return /^[a-z]$/.test(character);
}

/*
 * [GoalNode] and [TacticGroupNode] can react to responses. These methods assume
 * that [this] is the current node.
 */

GoalNode.prototype.reactTo = function(query, response) {

    var proofTree = this.proofTree;

    var trimmed = coqTrim(query);

    // if we are leaving the tree, no need to refresh
    if (_(['Qed.', 'Admitted.', 'Abort.', 'Defined.']).contains(trimmed)) {
        exitProofTree();
        return;
    }

    // don't create nodes for commands/bullets, but keep track of last response
    if (isVernacularCommand(trimmed) || isLtacBullet(trimmed)) {
        this.response = response;
        this.proofTree.refreshTactics();
        return;
    }

    switch (trimmed) {

    case "Proof.":
        this.response = response;
        this.proofTree.refreshTactics();
        //proofTreeQueryWish('{');
        return;

    case '{':
        this.response = response;
        this.proofTree.refreshTactics();
        this.openBraces++;
        return;

    case '}':
        this.closedBraces++;
        // try to solve the node again (will only work if properly unfocused)
        this.onSolved(response);
        return;

    case '+':
    case '-':
    case '*':
        this.response = response;
        this.proofTree.refreshTactics();
        return;

    }

    // The query can come from the user and have no tactic node
    var existingTactic = _(this.getTactics())
        .find(function(elt) { return elt.tactic === query; })
    ;

    if (existingTactic === undefined) {
        var groupToAttachTo = this.getUserTacticsGroup();
        var newChild = new TacticNode(
            proofTree,
            groupToAttachTo,
            query,
            response
        );
        groupToAttachTo.tactics.unshift(newChild);
        groupToAttachTo.tacticIndex = 0;
        existingTactic = newChild;
    }

    existingTactic.makeFocusedUptoGroup();
    proofTree.update()
        .then(function() {

            var unsolvedGoal = _(existingTactic.goals)
                .find(function(elt) { return !elt.isSolved(); })
            ;

            if (unsolvedGoal === undefined) {
                existingTactic.parent.onSolved(response);
            } else {
                unsolvedGoal.makeCurrentNode(response)
                    .then(function() {
                        proofTree.refreshTactics();
                        return Promise.resolve();
                    })
                    .then(proofTree.update.bind(proofTree))
                ;
            }

        });

}

TacticGroupNode.prototype.reactTo = function(query, response) {

    alert('tactic group node reacts to' + query);

}

/*
  Returns an array [n1, a, b, ..., z, n2]
  such that n1 -> a -> b -> ... -> z -> n2
  is the shortest path from n1 to n2 in the tree
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
  Returns an array [[g1, a, b, ..., z, g2]]
  such that g1 -> a -> b -> ... -> z -> g2
  is the shortest path from g1 to g2 in the tree
  and a, b, ... are all goals
  assumes [g1] and [g2] are [GoalNode]s
*/
function goalPath(g1, g2) {
    if (g1.id === g2.id) { return [g1]; }
    if (g1.depth < g2.depth) {
        var res = goalPath(g1, g2.parent.parent);
        res.push(g2);
        return res;
    } else if (g1.depth > g2.depth) {
        var res = goalPath(g1.parent.parent, g2);
        res.unshift(g1);
        return res;
    } else {
        var res = goalPath(g1.parent.parent, g2.parent.parent);
        res.unshift(g1);
        res.push(g2);
        return res;
    }
}

/*
 * [makeCurrentNode] should be the only way to set the current node from now on!
 * [response] is the response to store in the destination goal
 * [onGoalNode] will be called for each goal node traversed to reach [this]
 */
GoalNode.prototype.makeCurrentNode = function(response, onGoalNode) {

    var self = this;

    this.response = response;

    var path = goalPath(this.proofTree.curNode, this);

    return _(path).rest()
    // build a list of sparks
        .map(function(g) {
            return function() {
                return new Promise(function(onFulfilled, onRejected) {
                    self.proofTree.curNode = g;
                    self.proofTree.curNode.makeFocusedUptoGoal();
                    if (onGoalNode !== undefined) {
                        onGoalNode(g);
                    }
                    onFulfilled();
                });
            };
        })
    // then fire them in sequence
        .reduce(function(promiseAcc, promiseSpark) {
            return promiseAcc
                .then(promiseSpark())
                .then(self.proofTree.update.bind(self.proofTree))
            ;
        }, Promise.resolve())
    ;

}

/*
TacticGroupNode.prototype.makeCurrentNode = function() {
    this.proofTree.curNode = this;
    this.makeFocused();
}

TacticNode.prototype.makeCurrentNode = function() {
    throw 'Trying to make a tactic node the current node';
}
*/

/*
 * [click] should react to the node being clicked. The only nodes which should
 * be clicked are the current node's parent, the current node and:
 *
 * - if the current node is a tactic, its children
 *
 * - if the current node is a goal, its first child and this child's children
 *
 * A [TacticNode] can NOT be clicked as it does not appear visually. If it is
 * clicked programmatically, that is a mistake!
 */

ProofTree.prototype.undoUntilNode = function(dst) {
    // prevents infinite loops when user mashes Left
    if (activeProofTree.curNode.isRootNode()) {
        return Promise.resolve();
    }
    var self = this;
    return onCtrlUp(true)
        .then(function() {
            if (self.curNode.id === dst.id) {
                return Promise.resolve();
            } else {
                return self.undoUntilNode(dst);
            }
        });
}

GoalNode.prototype.click = function() {
    // if (this.isCurNodeChild()) {
    //     // TODO: if this is not the first unsolved child, add as many admits as
    //     // necessary?
    //     //proofTreeQueryWish('{');
    // } else if (this.isCurNodeParent()) {
    //     this.proofTree.undoUntilNode(this);
    // }
}

TacticGroupNode.prototype.click = function() {
    if (this.isCurNodeChild()) {
        var t = this.getFocusedTactic();
        proofTreeQueryWish(t.tactic);
    } else if (this.isCurNodeParent()) {
        this.proofTree.undoUntilNode(this.parent);
    }
}

/*
 * [response] is needed because solving this node might bring us to another node
 *  which needs to be updated with the last response it got
 */
GoalNode.prototype.onSolved = function(response) {
    if (this.openBraces === this.closedBraces) {
        if (this.hasParent()) {
            this.parent.onChildSolvedAndUnfocused(response);
        } else if (autoLayout) {
            proofTreeQueryWish('Qed.');
        }
    } else if (autoLayout) {
        proofTreeQueryWish('}');
    }
}

TacticGroupNode.prototype.onSolved = function(response) {
    var self = this;
    this.solved = true;
    this.parent.makeCurrentNode(response);
    this.proofTree.update()
        .then(function() {
            self.parent.onChildSolved(response);
        })
    ;
}

GoalNode.prototype.onChildSolved = function(response) {
    var self = this;
    this.solved = true;
    this.proofTree.update()
        .then(function() {
            self.onSolved(response);
        })
    ;
}

TacticGroupNode.prototype.onChildSolvedAndUnfocused = function(response) {
    var focusedTactic = this.getFocusedTactic();
    var unsolved = _(focusedTactic.goals)
        .find(function(elt) {
            return !elt.isSolved();
        })
    ;
    if (unsolved === undefined) {
        this.onSolved(response);
    } else {
        unsolved.makeCurrentNode(response);
        this.proofTree.refreshTactics();
        this.proofTree.update();
    }
}

/*
 * assumes [undone] has already been trimmed
 */

GoalNode.prototype.onUndo = function(fromUser, undone, response) {
    switch(undone) {
    case '{':
        this.openBraces--;
        break;

    case '}':
        if (this.closedBraces === 0) {
            /*
              This is tricky! Undoing this closing curly brace means we need to
              focus on the goal that was finished with that brace. It can be
              either the previous subgoal, or one of its last-descendants,
              depending on which levels were or weren't focused.
            */
            var parentTactic = this.parent.getFocusedTactic();
            parentTactic.goalIndex--;
            var previousSubgoal = parentTactic.goals[parentTactic.goalIndex];
            // now, there must be one rightmost descendant that has a
            // closedBraces > 0
            var subgoalToFocus = previousSubgoal.findLastClosed();
            subgoalToFocus.makeCurrentNode(response);
            subgoalToFocus.closedBraces--;
            this.proofTree.update();
        } else {
            // undoing curly brace for the current goal
            this.closedBraces--;
        }
        break;

    case 'Proof.':
        onCtrlUp(false);
        break;

    case '+':
    case '-':
    case '*':
        break;

    default:

        // TODO: there should be a safer way to detect this
        // if aborting proof
        if (_(theoremStarters).contains(getVernac(undone))) {
            exitProofTree();
            return;
        }

        // if it was a command
        if (isVernacularCommand(undone)) {
            this.proofTree.refreshTactics();
            return;
        }

        if (this.isSolved()) {
            // undoing the solving tactic
            this.unsolveLastSolved().makeCurrentNode(response);
            this.proofTree.update();
        } else {
            // undoing the tactic that led to this node
            // it can be either in the previous solved subgoal
            // or the parent goal
            var parentTactic = this.parentTactic;
            if (this.id === parentTactic.goals[0].id) {
                if (undone === this.parentTactic.tactic) {
                    this.parent.parent.makeCurrentNode(response);
                    this.proofTree.refreshTactics();
                    this.proofTree.update();
                } else {
                    alert(undone
                          + ' is not the same as parent tactic '
                          + this.parentTactic.tactic);
                }
            } else {
                /*
                  [this] is not the first goal of its parent tactic, we must go
                  back to the last goal of the previous subgoal
                */
                parentTactic.goalIndex--;
                var previousSubgoal = parentTactic.goals[parentTactic.goalIndex];
                var subgoalToFocus = previousSubgoal.unsolveLastSolved();
                subgoalToFocus.makeCurrentNode(response);
                this.proofTree.update();
            }
        }

        break;
    }

}

/*
 * Returns the goal node that was last closed, starting from a node, and
 * recursively searching through its last subgoals.
 */
GoalNode.prototype.findLastClosed = function() {
    if (this.closedBraces > 0) {
        return this;
    } else {
        var focusedTacticGroup = this.getFocusedTacticGroup();
        var focusedTactic = focusedTacticGroup.getFocusedTactic();
        var lastSubgoal = focusedTactic.goals[focusedTactic.goals.length - 1];
        return lastSubgoal.findLastClosed();
    }
}

/*
 * Returns the last goal node that was solved. Also marks unsolved all the nodes
 * on the way.
 */
GoalNode.prototype.unsolveLastSolved = function() {
    this.solved = false;
    var focusedTacticGroup = this.getFocusedTacticGroup();
    focusedTacticGroup.solved = false;
    var focusedTactic = focusedTacticGroup.getFocusedTactic();
    if (focusedTactic.goals.length === 0) {
        return this;
    } else {
        var subgoal = focusedTactic.goals[focusedTactic.goals.length - 1];
        return subgoal.unsolveLastSolved();
    }
}

TacticGroupNode.prototype.shiftNextInGroup = function() {
    if (this.tacticIndex < this.tactics.length - 1) {
        this.tacticIndex++;
        asyncLog("NEXTGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]));
        this.proofTree.update();
    }
}

TacticGroupNode.prototype.shiftPrevInGroup = function() {
    if (this.tacticIndex > 0) {
        this.tacticIndex--;
        asyncLog("PREVGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]));
        this.proofTree.update();
    }
}

Node.prototype.isRootNode = function() {
    return this.proofTree.rootNode.id === this.id;
}

function isConjunction(t) {
    return (
        t.tag === "App"
            && t.contents[0].tag === "App"
            && t.contents[0].contents[0].tag === "Var"
            && t.contents[0].contents[0].contents === "and"
    );
}

function isDisjunction(t) {
    return (
        t.tag === "App"
            && t.contents[0].tag === "App"
            && t.contents[0].contents[0].tag === "Var"
            && t.contents[0].contents[0].contents === "or"
    );
}

ProofTree.prototype.hypIsDisjunction = function(h) {
    return isDisjunction(h.hType);
}

ProofTree.prototype.hypIsConjunction = function(h) {
    return isConjunction(h.hType);
}

ProofTree.prototype.goalIsConjunction = function() {
    return isConjunction(this.curNode.goalTerm);
}

ProofTree.prototype.goalIsDisjunction = function() {
    return isDisjunction(this.curNode.goalTerm);
}

ProofTree.prototype.goalIsForall = function() {
    return this.curNode.goalTerm.tag === "Forall";
}

ProofTree.prototype.goalIsExists = function() {
    return this.curNode.goalTerm.tag === "Exists";
}

ProofTree.prototype.goalIsReflexive = function() {
    var goalTerm = this.curNode.goalTerm;
    return (
        goalTerm.tag === "App"
            && goalTerm.contents[0].tag === "App"
            && goalTerm.contents[0].contents[0].tag === "Var"
            && goalTerm.contents[0].contents[0].contents === "eq"
            && _.isEqual(goalTerm.contents[1], goalTerm.contents[0].contents[1])
    );
}

ProofTree.prototype.getAncestorTactics = function() {
    var ancestorTacticsOf = function(goalNode) {
        if (goalNode.parentTactic !== undefined) {
            var rec = ancestorTacticsOf(goalNode.parent.parent);
            rec.push(goalNode.parentTactic);
            return rec;
        } else {
            return [];
        }
    };

    return ancestorTacticsOf(this.curNode);
}

function allDescendantTactics(tacticNode) {
    return _(tacticNode.goals)
        .reduce(function(acc, g) {
            var focusedTacticGroup = g.getFocusedTacticGroup();
            if (!focusedTacticGroup) { return acc; }
            var processedTactic =
                focusedTacticGroup.tactics[focusedTacticGroup.tacticIndex];
            return acc.concat(allDescendantTactics(processedTactic));
        }, [tacticNode])
    ;
}

function priorDescedantTactics(tacticNode) {
    if (!tacticNode.goals) { return []; }
    var goalsToGatherFrom = _(tacticNode.goals).slice(0, tacticNode.goalIndex);
    return goalsToGatherFrom
        .reduce(function(acc, g) {
            var focusedTacticGroup = g.getFocusedTacticGroup();
            if (!focusedTacticGroup) { return acc; }
            var processedTactic =
                focusedTacticGroup.tactics[focusedTacticGroup.tacticIndex];
            return acc.concat(allDescendantTactics(processedTactic));
        }, [tacticNode])
    ;
}

/*
  Lists all the tactics that have been processed in the current proof state. This
  includes all the ancestor tactics of the current node, and for each of those,
  all their descendant tactics for goals inferior than the one at the current index
*/
ProofTree.prototype.getProcessedTactics = function() {
    var ancestorTactics = this.getAncestorTactics();
    return _(ancestorTactics).reduce(function(acc, a) {
        return acc.concat(priorDescedantTactics(a));
    }, []);
}
