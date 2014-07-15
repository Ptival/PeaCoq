
/*
TODO:
- make it so that each instance has its own tactic set
*/

// CONFIGURATION
var nodeMinSpacing = 5;
var nodeStroke = 2;
var nodeHeight = 25;
var rectMargin = {top: 2, right: 8, bottom: 2, left: 8};
var scrollbarWidth = 0; // I could compute this if I cared enough
var nbChildrenToShow = 2;
var animationDuration = 420;

// OTHER GLOBALS
var i = 1; // unique identifier, should closure it to avoid drama
var maxNodesOnLine = Math.pow(nbChildrenToShow, 2);
var diagonal = d3.svg.diagonal();
var rootId = i++;
var animationRunning = false;

// GLOBALS TO BE INITIALIZED LATER
var tree, svg, canvas, context;
var smallestNodeWidth, width, height, curNode, rootNode;
var xFactor, yFactor;

var thms = [
'Theorem plus_O_n : ∀n : nat, 0 + n = n.',
'Theorem plus_1_l : ∀n : nat, 1 + n = S n.',
'Theorem mult_0_l : ∀n : nat, 0 * n = 0.',
'Theorem plus_id_example : ∀n m:nat, n = m → n + n = m + m.',
'Theorem plus_id_exercise : ∀n m o : nat, n = m → m = o → n + m = m + o.',
'Theorem mult_0_plus : ∀n m : nat, (0 + n) * m = n * m.',
'Theorem mult_S_1 : ∀n m : nat, m = S n → m * (1 + n) = m * m.',
'Theorem negb_involutive : ∀b : bool, negb (negb b) = b.',
'Theorem identity_fn_applied_twice : ∀(f : bool → bool), (∀(x : bool), f x = x) → ∀(b : bool), f (f b) = b.',
'Theorem andb_eq_orb : ∀(b c : bool), (andb b c = orb b c) → b = c.',
'Theorem andb_true_elim1 : ∀b c : bool, andb b c = true → b = true.',
'Theorem andb_true_elim2 : ∀b c : bool, andb b c = true → c = true.',
'Theorem plus_0_r : ∀n:nat, n + 0 = n.',
'Theorem minus_diag : ∀n, minus n n = 0.',
'Theorem mult_0_r : ∀n:nat, n * 0 = 0.',
'Theorem plus_n_Sm : ∀n m : nat, S (n + m) = n + (S m).',
'Theorem plus_comm : ∀n m : nat, n + m = m + n.',
'Theorem plus_assoc : ∀n m p : nat, n + (m + p) = (n + m) + p.',
'Theorem plus_rearrange : ∀n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).',
'Theorem plus_swap : ∀n m p : nat, n + (m + p) = m + (n + p).',
'Theorem mult_comm : ∀m n : nat, m * n = n * m.',
'Theorem andb_false_r : ∀b : bool, andb b false = false.',
'Theorem mult_1_l : ∀n:nat, 1 * n = n.',
'Theorem all3_spec : ∀b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.',
'Theorem mult_plus_distr_r : ∀n m p : nat, (n + m) * p = (n * p) + (m * p).',
'Theorem mult_assoc : ∀n m p : nat, n * (m * p) = (n * m) * p.',
];

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

function nodeWidth(d) {
    return smallestNodeWidth
        //* ((isCurNode(d) || isCurNodeParent(d)) ? nbChildrenToShow : 1)
    ;
}

function treeDepth(root) {
    return (
        root.visibleChildren
            ? 1 + _(root.visibleChildren).map(treeDepth).max()
            : 0
    );
}

function addTheorem(theorem) {
    var b = $('<button>', {
        text: theorem,
        click: function() { newTheorem(theorem); }
    });
    $('#buttons').append(b);
}

$(document).ready(function() {
    _(thms).each(addTheorem);

    smallestNodeWidth = evenFloor(
        ($(window).width()
         - scrollbarWidth
         - ((maxNodesOnLine - 1) * nodeMinSpacing)
        )
        / maxNodesOnLine
    );
    width =
        maxNodesOnLine * smallestNodeWidth
        + (maxNodesOnLine - 1) * nodeMinSpacing;
    // now that the buttons are here, we can compute the remaining height
    height = $(window).height() - ($('#tips').height() + $('#buttons').height());
    xFactor = width;
    yFactor = height;

    newTheorem(thms[16], hInit);
});

function newTheorem(theorem) {
    d3.select("svg").remove();

    tree = d3.layout.tree()
        .children(function(d) {
            if (d.solved) { return []; }
            if (isCurNode(d)) { return d.allChildren; }
            if (isCurNodeParent(d) && isTactic(d)) { return d.allChildren; }
            return d.visibleChildren;
        })
        .separation(function(n1, n2) {
            //if (isCurNode(n1) || isCurNode(n2)) { return nbChildrenToShow; }
            return 1;
        })
    ;

    svg = d3.select("body")
        .on("keydown", function() {
            if (animationRunning) { return; }
            //console.log(d3.event);
            var event = null;
            if (d3.event.hasOwnProperty('keyIdentifier')) { // Chrome
                event = d3.event.keyIdentifier;
            } else if ('key' in d3.event) { // Firefox
                event = d3.event.key;
            }
            switch (event) {
            case "Left": shiftLeft(curNode); break;
            case "Right": shiftRight(curNode); break;
            case "Up":
                if(hasParent(curNode)) {
                    click(curNode.parent);
                }
                break;
            case "Down":
                if (isTactic(curNode)) {
                    var dest = _(curNode.visibleChildren).find(function(n) {
                        return !(n.solved);
                    });
                    if (dest) { click(dest); }
                } else {
                    if (curNode.visibleChildren[0]) { click(curNode.visibleChildren[0]); }
                }
                break;
            case "U+0031": case "U+0041":
                if (curNode.visibleChildren[0]) { click(curNode.visibleChildren[0]); }
                break;
            case "U+0032": case "U+0042":
                if (curNode.visibleChildren[1]) { click(curNode.visibleChildren[1]); }
                break;
            case "U+0033": case "U+0043":
                if (curNode.visibleChildren[2]) { click(curNode.visibleChildren[2]); }
                break;
            default: return;
            }
            // Prevent arrows from scrolling the webpage
            d3.event.preventDefault();
        })
        .insert("svg", ":first-child")
        .attr("width", width)
        .attr("height", height)
    ;

    canvas =
        svg
        .append("g")
        .attr("id", "viewport")
        .attr("class", "canvas")
    // an okay approximation of the canvas initial translation
        .attr("transform",
              "translate("
              + width / maxNodesOnLine
              + ", "
              + 0
              + ")"
             )
    ;

    context =
        svg
        .append("g")
        .attr("class", "context")
    ;

    var contextWidth = smallestNodeWidth - rectMargin.left - rectMargin.right;
    var contextHeight;

    context
        .append("foreignObject")
        .attr('x', rectMargin.left)
    // fix the width
        .attr("width", smallestNodeWidth - rectMargin.left - rectMargin.right)
    // render
        .html('<div><p>Empty context</p></div>')
    // now retrieve the computed height of the div
        .attr("height", function() {
            contextHeight = this.firstChild.getBoundingClientRect().height
            return contextHeight;
        })
    ;

    context
        .insert("rect", ":first-child")
        .attr("width", contextWidth)
        .attr("height", contextHeight)
    ;

    debug =
        svg
        .append("g")
        .attr("class", "debug")
    ;

    var debugWidth = smallestNodeWidth - rectMargin.left - rectMargin.right;
    var debugHeight;

    debug
        .append("foreignObject")
        .attr('x', width - smallestNodeWidth + rectMargin.left)
    // fix the width
        .attr("width", smallestNodeWidth - rectMargin.left - rectMargin.right)
    // render
        .html('<div><p>No debug information</p></div>')
    // now retrieve the computed height of the div
        .attr("height", function() {
            debugHeight = this.firstChild.getBoundingClientRect().height
            return debugHeight;
        })
    ;

    debug
        .insert("rect", ":first-child")
        .attr("x", width - smallestNodeWidth)
        .attr("width", debugWidth)
        .attr("height", debugHeight)
    ;

    svg
        .insert("script", ":first-child")
        .attr("xlink:href", "SVGPan.js")
    ;

    syncQuery('Abort All.', hIgnore);
    syncQuery(theorem, hInit);

}

function mkGoalNode(g, ndx) {
    return {
        "id": i++,
        "name": g.gGoal,
        "hyps": g.gHyps,
        "ndx": ndx + 1,
        "gid": g.gId,
        "offset": 0,
    };
}

function mkTacticNode(t) {
    var children = _(t[1])
        .map(mkGoalNode)
        .value()
    ;

    return {
        "id": i++,
        "name": t[0],
        "allChildren": children,
        "visibleChildren": children.slice(0, nbChildrenToShow),
        "offset": 0,
    };
}

function hInit(response) {

    //console.log(response);

    // There should only be one goal at that point
    rootNode = {
        "id": rootId,
        "name": response.currentGoals.focused[0].gGoal,
        "x0": 0.5,
        "y0": 0,
        "allChildren": _(response.nextGoals)
            .map(mkTacticNode)
            .value(),
        "ndx": 1,
        "depth": 0, // need to set depth for isGoal() to work early
        "offset": 0,
    };

    curNode = rootNode;

    click(rootNode);

    update(rootNode);

}

function hasParent(n) {
    return (n.hasOwnProperty('parent'));
}

function hasGrandParent(n) {
    return (n.hasOwnProperty('parent')
            && n.parent.hasOwnProperty('parent'));
}

function isCurNode(n) { return (n.id === curNode.id); }

function isCurNodeParent(n) {
    return (hasParent(curNode) && curNode.parent.id === n.id);
}

function isCurNodeChild(n) {
    if (hasParent(n) && isCurNode(n.parent)) { return true; }
    return false;
}

function isCurNodeGrandChild(n) {
    if (hasParent(n) && isCurNodeChild(n.parent)) { return true; }
    return false;
}

function update(source) {

    // if the viewpoint has been zoomed, cancel the zoom so that the computed
    // sizes are correct
    var m = parseSVGTransform(canvas.attr('transform'));
    if (m.hasOwnProperty('matrix')) {
        m = m.matrix;
        canvas.attr('transform',
                    'matrix(1'
                    + ',' + m[1]
                    + ',' + m[2]
                    + ', 1'
                    + ',' + m[4]
                    + ',' + m[5]
                    +')')
        ;
    }

    var nodes = tree.nodes(rootNode);
    var links = tree.links(nodes);

    var node =
        canvas
        .selectAll("g.node")
        .data(nodes, function(d) {
            return d.id || (d.id = i++);
        })
    ;

    var link =
        canvas
        .selectAll("path")
        .data(links, function(d) {
            return d.id = d.source.id + "," + d.target.id;
        });

    var nodeEnter = node.enter();

    var gs = nodeEnter
        .append("g")
        .attr("class", "node")
        .on("click", click)
    ;

    gs
        .append("foreignObject")
    // fix the width
        .attr("width", function(d) {
            return nodeWidth(d) - rectMargin.left - rectMargin.right;
        })
    // render the div
        .html(function(d) {
            if (isGoal(d)) {
                var hyps = '';

                if (hasGrandParent(d)) {
                    var gpHyps = d.parent.parent.hyps;
                    _(gpHyps).each(function(h) {
                        if (!_(d.hyps).contains(h)) {
                            hyps = hyps
                                + '<span class="diff-minus">⊖ ' + h + '</span><br/>';
                        }
                    });
                    _(d.hyps).each(function(h) {
                        if (!_(gpHyps).contains(h)) {
                            hyps = hyps
                                + '<span class="diff-plus">⊕ ' + h + '</span><br/>';
                        }
                    });
                } else {
                    _(d.hyps).each(function(h) {
                        hyps = hyps + '<span>' + h + '</span><br/>';
                    });
                }

                return '<div class="node">'
                    + ((hyps !== '') ? (hyps + '<hr/>') : '')
                    + '<span>'
                    + d.name
                    + '</span></div>';
            } else {
                return '<div class="node"><span>'
                    + d.name
                    + '</span></div>'
            }
        })
    // now retrieve the computed height of the div
        .attr("height", function(d) {
            var h = this.firstChild.getBoundingClientRect().height;
            d.height = h + 2 * nodeStroke;
            return h;
        })
        .attr("transform", function(d) {
            return 'translate(-'
                + ((nodeWidth(d) / 2) - rectMargin.left)
                + ', -'
                + ((d.height / 2) - rectMargin.top)
                + ')'
            ;
        })
    ;

    // Compute the new visible nodes, determine the translation and zoom

    var visibleNodes = [];
    visibleNodes = visibleNodes.concat(curNode.parent || []);
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
    var gcSiblings = _.zip(allGrandChildren.value(), allGrandChildren.rest().value());
    gcSiblings.pop(); // removes [gc_last, undefined] at the end
    var cSiblings = _.zip(allChildren.value(), allChildren.rest().value());
    cSiblings.pop(); // removes [c_last, undefined] at the end
    var siblings = gcSiblings.concat(cSiblings);

    var siblingsDistances = siblings.map(function(e) {
        return (e[1].x - e[0].x);
    });

    var siblingMinDistance = _.min(siblingsDistances);

    xFactor = (siblingMinDistance === Infinity)
        ? xFactor
        : ((smallestNodeWidth + nodeMinSpacing)
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

    yFactor = (dY === 0)
        ? yFactor
        : ((height - (topmostNode.height / 2) - (bottommostNode.height / 2)) / dY)
    ;

    gs
        .attr("transform", function(d) {
            if (hasParent(d)) {
                // non-roots are spawned at their parent's (cX0, cY0)
                d.cX0 = d.parent.cX0;
                d.cY0 = d.parent.cY0;
            } else {
                // the root stores its own (x0, y0)
                d.cX0 = d.x0 * xFactor;
                d.cY0 = d.y0 * yFactor;
            }
            return "translate(" + d.cX0 + "," + d.cY0 + ")";
        })

    gs
        .insert("rect", ":first-child")
        .attr("x", function(d) {
            return this.nextSibling.getBBox().x - nodeWidth(d) / 2;
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
                shiftLeft(n);
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
            shiftRight(n);
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
                    && (isCurNode(d) || isCurNodeChild(d))
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
                    && (isCurNode(d) || isCurNodeChild(d))
                    && !_.isEmpty(d.visibleChildren)
            );
        })
    ;

    // All the nodes need to move to their new position, according to the
    // new tree layout and the new zoom factors

    // We want
    // (firstChild.cX + lastChild.cX) / 2 = curNode.cX
    // We offset all the descendants to achieve this
    var xMiddle =
        (firstVisibleChild !== undefined && lastVisibleChild !== undefined)
        ? (firstVisibleChild.x + lastVisibleChild.x) / 2
        : curNode.x
    ;

    var descendantsXOffset = curNode.x - xMiddle;

    _(nodes)
        .each(function(n) {
            if (isCurNodeChild(n) || isCurNodeGrandChild(n)) {
                n.cX = (n.x + descendantsXOffset) * xFactor;
            } else {
                n.cX = n.x * xFactor;
            }
            n.cY = n.y * yFactor;
        })
    ;

    canvas
        .transition()
        .duration(animationDuration)
        .attr("transform",
              "translate("
              + (
                  width / 2 - curNode.cX
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
                      : (topmostNode.height / 2 - minY * yFactor)
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
        .attr("width", nodeWidth)
        .attr("x", function(d) {
            return this.nextSibling.getBBox().x - nodeWidth(d) / 2;
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
            return nodeWidth(d) - rectMargin.left - rectMargin.right;
        })
        .attr("transform", function(d) {
            return 'translate(-'
                + ((nodeWidth(d) / 2) - rectMargin.left)
                + ', -'
                + ((d.height / 2) - rectMargin.top)
                + ')'
            ;
        })
/* TODO: this seems not to work, is the height registered once on transition
   triggering instead of being recomputed at each step?

        .attr("height", function(d) {
            var h = this.firstChild.getBoundingClientRect().height;
            d.height = h + 2 * nodeStroke;
            return h;
        })
*/
    ;

    canvas
        .selectAll("rect")
        .classed("tactic", function(d) { return isTactic(d) && !d.solved; })
        .classed("goal", function(d) { return isGoal(d) && !d.solved; })
        .classed("solved", function(d) { return (d.solved); })
        .classed("current", isCurNode)
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
            var parentAlsoExiting = nodeIsExiting(d.parent);
            var nodeToReach = parentAlsoExiting ? d.parent.parent : d.parent;
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
            var sourceNode = sourceAlsoExiting ? d.source.parent : d.source;
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

    updateContext();

    animationRunning = true;
    window.setTimeout(function() { animationRunning = false; }, animationDuration);

}

function updateVisibleChildren(n) {
    n.visibleChildren = n.allChildren.slice(n.offset, n.offset + nbChildrenToShow);
    update(n);
}

function shiftLeft(n) {
    if (n.solved) { return; }
    if (n.offset > 0) {
        n.offset--;
        updateVisibleChildren(n);
    }
}

function shiftRight(n) {
    if (n.solved) { return; }
    if (n.offset + nbChildrenToShow < n.allChildren.length) {
        n.offset++;
        updateVisibleChildren(n);
    }
}

function click(d) {
    if (animationRunning) { return; }
    navigateTo(d);
    if (d.solved) { return; }

    if (!d.hasOwnProperty('allChildren') || d.allChildren.length === 0) {
        if (isGoal(d)) {
            syncQuery('Show.', function(response) {
                d.allChildren =
                    _(response.nextGoals)
                    .map(mkTacticNode)
                    .value()
                ;
            });
        }
        // otherwise, this is a terminating tactic for this goal!
        else {
            solved(d);
        }
    }

    expand(d);
    update(d);

/*
    // when the user clicks on a tactic node, bring them to the first goal
    if(isTactic(d) && d.allChildren[0]) {
        click(d.allChildren[0]);
    }
*/

}

// called when n has been solved
function solved(n) {
    n.solved = true
    n.visibleChildren = [];
    // WARNING: if you uncomment the following line, you need to change
    // the detection of nodes that need to be 'Undo'ne multiple times
    // n.allChildren = [];
    collapse(n);
    if (hasParent(n)) {
        navigateTo(n.parent);
        animationRunning = true;
        window.setTimeout(function () {
            childSolved(n.parent);
            update(n.parent);
            animationRunning = false;
        }, animationDuration);
    }
}

// called when a child of n has become solved
function childSolved(n) {
    if (isGoal(n)) {
        solved(n);
    } else {
        // Bubble up if this was the last subgoal
        var lastSubgoal =
            _(n.allChildren)
            .every(function(n) { return n.solved === true })
        ;
        if (lastSubgoal) { solved(n); }
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

function expand(d) {
    d.visibleChildren = d.allChildren.slice(d.offset, d.offset + nbChildrenToShow);
    if (isGoal(d)) {
        _(d.visibleChildren)
            .each(function(c) {
                c.visibleChildren = c.allChildren.slice(c.offset, c.offset + nbChildrenToShow);
            });
    }
}

function commonAncestor(n1, n2) {
    if (n1.id === rootNode.id || n2.id === rootNode.id) { return rootNode; }
    if (n1.id === n2.id) { return n1; }
    if (n1.depth < n2.depth) {
        return commonAncestor(n1, n2.parent);
    } else if (n1.depth > n2.depth) {
        return commonAncestor(n1.parent, n2);
    } else {
        return commonAncestor(n1.parent, n2.parent);
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

function navigateTo(dest) {

    var a = commonAncestor(curNode, dest);

    var p = path(curNode, dest);

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
                    // TODO: actually, need to Undo as many times as the
                    // focus depth difference between before and after the tactic...
                    if(src.allChildren.length === 0) {
                        syncQuery('Undo.', hIgnore);
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
                    collapseExcept(src, dst);
                }

                if (isTactic(dst)) {
                    syncQuery(dst.name, hIgnore);
                } else {
                    syncQuery('Focus ' + dst.ndx + '.', hIgnore);
                }

            }
        })
    ;

    curNode = dest;

}

function isTactic(n) { return (n.depth % 2 === 1); }

function isGoal(n) { return (n.depth % 2 === 0); }

function syncQuery(q, h) {
    console.log(q);
    $.ajax({
        type: 'POST',
        url: 'query',
        data: {query : q},
        async: false,
        success: function(response) {
            updateDebug(response);
            h(response);
        }
    });
}

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
            context
                .select('rect')
                .attr('height', height)
            ;
            return height;
        })
    ;
}

function updateContext() {

    var contextDiv = context.select('div');
    var curGoal = (isGoal(curNode)) ? curNode : curNode.parent;
    var curHyps = curGoal.hyps;

    contextDiv.html("");

    if (hasGrandParent(curGoal)) {
        _(curHyps).each(function(h) {
            contextDiv
                .append('p')
                .text(h);
            ;
        });
    } else {
        _(curHyps).each(function(h) {
            contextDiv
                .append('p')
                .text(h);
            ;
        });
    }

    if (contextDiv.html() === "") {
        contextDiv.append("p").text("Empty context");
    }

    updateNodeHeight(context);

}

function updateDebug(response) {

    var debugDiv = debug.select('div');
    if (response.currentGoals.focused.length > 0) {
        debugDiv.html(response.currentGoals.focused[0].gGoal);
    } else {
        debugDiv.html(response.coqtopResponse.contents[0]);
    }

    updateNodeHeight(debug);

}
