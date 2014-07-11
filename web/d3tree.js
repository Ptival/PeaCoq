
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
var animationDuration = 500;

// OTHER GLOBALS
var i = 1; // unique identifier, should closure it to avoid drama
var maxNodesOnLine = Math.pow(nbChildrenToShow, 2);
var diagonal = d3.svg.diagonal();
var rootId = i++;
var animationRunning = false;

// GLOBALS TO BE INITIALIZED LATER
var tree, svg, canvas;
var smallestNodeWidth, width, height, curNode, rootNode;
var xFactor, yFactor;

var thms = [
'Theorem trivial : ∀ c : comparison, True.',
'Theorem plus_O_n : ∀ n : nat, 0 + n = n.',
'Theorem plus_1_l : ∀ n : nat, 1 + n = S n.',
'Theorem mult_0_l : ∀ n : nat, 0 * n = 0.',
'Theorem plus_id_example : ∀n m:nat, n = m → n + n = m + m.',
'Theorem plus_id_exercise : ∀ n m o : nat, n = m → m = o → n + m = m + o.',
'Theorem mult_0_plus : ∀ n m : nat, (0 + n) * m = n * m.',
'Theorem mult_S_1 : ∀n m : nat, m = S n → m * (1 + n) = m * m.',
//'Theorem plus_1_neq_0 : ∀ n : nat, beq_nat (n + 1) 0 = false.',
'Theorem negb_involutive : ∀ b : bool, negb (negb b) = b.',
//'Theorem zero_nbeq_plus_1 : ∀ n : nat, beq_nat 0 (n + 1) = false.',
'Theorem identity_fn_applied_twice : ∀(f : bool → bool), (∀(x : bool), f x = x) → ∀(b : bool), f (f b) = b.',
'Theorem andb_eq_orb : ∀(b c : bool), (andb b c = orb b c) → b = c.'
];

function evenFloor(x) {
    var r = Math.floor(x);
    return (r % 2 == 0) ? r : r - 1;
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

    newTheorem(thms[0], hInit);
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
            switch (d3.event.keyIdentifier) {
            case "Left": shiftLeft(curNode); break;
            case "Right": shiftRight(curNode); break;
            case "Up":
                if(curNode.hasOwnProperty('parent')) {
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

function isCurNode(n) { return (n.id == curNode.id); }

function isCurNodeParent(n) {
    return (curNode.hasOwnProperty('parent') && curNode.parent.id == n.id);
}

function isCurNodeChild(n) {
    if (n.hasOwnProperty('parent') && n.parent.id == curNode.id) { return true; }
    return false;
}

function update(source) {

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
            // Note: you can't only replace the first comma, because of
            // (∀ x, P x) → Q
              return '<div class="node"><span>'
                + d.name
                + '</span></div>';
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

    var children = _(curNode.visibleChildren);

    var grandChildren = _(children).map(function(c) {
        if (c.hasOwnProperty('visibleChildren')) {
            return _(c.visibleChildren).value();
        }
        return [];
    }).flatten();

    var firstGrandChild = grandChildren.first();
    var firstChild = children.first();

    var leftmostNode = firstGrandChild;
    if (leftmostNode == undefined) { leftmostNode = firstChild; }
    if (leftmostNode == undefined) { leftmostNode = curNode; }

    var lastGrandChild = grandChildren.last();
    var lastChild = children.last();

    var rightmostNode = grandChildren.last();
    if (rightmostNode == undefined) { rightmostNode = children.first(); }
    if (rightmostNode == undefined) { rightmostNode = curNode; }

    // We need to scale the view so that two adjacent nodes do not overlap and
    // are well spaced.

    // siblings = [ [gc0, gc1], [gc1, gc2], ... ] ++ [ [c0, c1], [c1, c2], ... ]
    var gcSiblings = _.zip(grandChildren.value(), grandChildren.rest().value());
    gcSiblings.pop(); // removes [gc_last, undefined] at the end
    var cSiblings = _.zip(children.value(), children.rest().value());
    cSiblings.pop(); // removes [c_last, undefined] at the end
    var siblings = gcSiblings.concat(cSiblings);

    var siblingsDistances = siblings.map(function(e) {
        return (e[1].x - e[0].x);
    });

    var siblingMinDistance = _.min(siblingsDistances);

    xFactor = (siblingMinDistance == Infinity)
        ? xFactor
        : ((smallestNodeWidth + nodeMinSpacing)
           / siblingMinDistance)
    ;

    // the top-most node is always the parent if it exists, the current otherwise
    var topmostNode = curNode.hasOwnProperty('parent') ? curNode.parent : curNode;

    // the bottom-most node is either the grand-child of largest height
    var bottommostNode =
        grandChildren.max(function(c) { return c.height; }).value();
    // or the child of largest height
    if (bottommostNode == -Infinity) {
        bottommostNode = children.max(function(c) { return c.height; }).value();
    }
    // or the current node
    if (bottommostNode == -Infinity) { bottommostNode = curNode; }

    yFactor = (dY == 0)
        ? yFactor
        : ((height - (topmostNode.height / 2) - (bottommostNode.height / 2)) / dY);

    gs
        .attr("transform", function(d) {
            if (d.hasOwnProperty('parent')) {
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
        .selectAll('.leftarrow')
        .classed('invisible', function(d) {
            return !(
                // visible when:
                !d.solved && d.offset > 0 && (isCurNode(d) || isCurNodeChild(d))
            );
        })
    ;

    node
        .selectAll('.rightarrow')
        .classed('invisible', function(d) {
            return !(
                // visible when:
                ! d.solved
                && d.offset + nbChildrenToShow < _(d.allChildren).size()
                && (isCurNode(d) || isCurNodeChild(d))
            );
        })
    ;

    // All the nodes need to move to their new position, according to the
    // new tree layout and the new zoom factors

    _(nodes)
        .each(function(n) {
            if (isCurNode(n) || isCurNodeParent(n)) {
                // We move these two nodes around the focused children
                var v = _(curNode.visibleChildren);
                if (v.first() == undefined) {
                    n.cX = n.x * xFactor;
                } else {
                    var centerX = (v.first().x + v.last().x) / 2;
                    n.cX = centerX * xFactor;
                }
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
                  (dX == 0)
                      ? (width / 2 - minX * xFactor)
                      : (smallestNodeWidth / 2 - minX * xFactor)
*/
              )
              + ", "
              + (
                  (dY == 0)
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
            if (n1.id == n2.id) { exiting = true; }
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

function contains(container, thing) { return (container.indexOf(thing) > -1); }

function nbDashes(s) {
    var n = s.match(/-/g);
    return (n || []).length;
}

function click(d) {

    if (animationRunning) { return; }

    navigateTo(d);

    if (d.solved) { return; }

    if (!d.allChildren || d.allChildren.length == 0) {

        if (isGoal(d)) {
            syncQuery('Show.', function(response) {

                //console.log(response);

                d.allChildren = _(response.nextGoals)
                    .map(mkTacticNode)
                    .value();

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
    n.solved = true;
    collapse(n);
    if (n.hasOwnProperty('parent')) {
        navigateTo(n.parent);
        window.setTimeout(function () {
            childSolved(n.parent);
            update(n.parent);
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
            .every(function(n) { return n.solved == true })
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
    if (n1.id == rootNode.id || n2.id == rootNode.id) { return rootNode; }
    if (n1.id == n2.id) { return n1; }
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
    if (n1.id == n2.id) { return [n1]; }
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
                    // need to Undo twice for terminating tactics
                    if(src.allChildren.length == 0) {
                        syncQuery('Undo.', hLog);
                    }
                    syncQuery('Undo.', hLog);
                } else {
                    // 'Back.' does not work in -ideslave
                    // 'Back.' takes one step to undo 'Show.'
                    // 'Undo.' works in -ideslave
                    // 'Undo.' does not care about 'Show.' commands

                    // Undo the 'Focus.' command.
                    // Do not use 'Unfocus.' as it is itself undone by 'Undo.'
                    syncQuery('Undo.', hLog);
                }
            } else { // going down

                // hide sibling tactic nodes
                if (isGoal(src)) {
                    collapseExcept(src, dst);
                }

                if (isTactic(dst)) {
                    syncQuery(dst.name, hLog);
                } else {
                    syncQuery('Focus ' + dst.ndx + '.', hLog);
                }

            }
        })
    ;

    curNode = dest;

}

function isTactic(n) { return (n.depth % 2 == 1); }

function isGoal(n) { return (n.depth % 2 == 0); }

function syncQuery(q, h) {
    console.log(q);
    $.ajax({
        type: 'POST',
        url: 'query',
        data: {query : q},
        async: false,
        success: h
    });
}

function hLog(response) {
    //console.log(response);
}

function hIgnore(response) {
}
