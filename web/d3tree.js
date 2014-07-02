
/*
TODO:
- bug where a terminating tactic does not show up green
*/

var i = 1; // unique identifier

var margin = {top: 20, right: 240, bottom: 20, left: 240};
var scrollbarWidth = 20; // I could compute this if I cared enough
var width = $(window).width() - (scrollbarWidth + margin.left + margin.right);
var height = 200;
var rectMargin = {top: 2, right: 8, bottom: 2, left: 8};
var xFactor = 1;
var yFactor = 1;

var tree, svg, canvas;

var diagonal = d3.svg.diagonal();

var curNode = null;

var rootId = i++;

var rootNode = null;

var thms = [
    'Theorem plus_0_r : forall x, x + 0 = x.',
    'Theorem plus_comm : ∀n m : nat, n + m = m + n.',
    'Theorem mult_0_r : ∀n:nat, n * 0 = 0.',
    'Theorem plus_assoc : ∀n m p : nat, n + (m + p) = (n + m) + p.',
];

function treeDepth(root) {
    return (
        root.children
            ? 1 + _(root.children).map(treeDepth).max()
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
    newTheorem(thms[0], hInit);
});

function newTheorem(theorem) {

    d3.select("svg").remove();

    tree = d3.layout.tree()

        .separation(function(n1, n2) {
            if (n1.id == n2.id || n1.depth != n2.depth) { return 1; }
            // This is just a heuristic...
            return (n1.name.length + n2.name.length) / (1 + n1.depth * n2.depth);
        })
    ;

    svg = d3.select("body")
        .style("margin", 0)
        .append("svg")
        .attr("width", margin.left + width + margin.right)
        .attr("height", margin.top + height + margin.bottom)
        .style("border", "1px solid black")
    ;

    canvas =
        svg
        .append("g")
        .attr("id", "viewport")
        .attr("class", "canvas")
        .attr("transform", "translate(" + margin.left + ", " + margin.top + ")")
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
        "_children": children,
        "children": children,
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
        "_children": _(response.nextGoals)
            .map(mkTacticNode)
            .value(),
        "ndx": 1,
    };

    curNode = rootNode;

    click(rootNode);

    update(rootNode);

}

/*
function getClosestAncestorCoord0(n) {
    if (!n.hasOwnProperty('parent')) { return [n.cX0, n.cY0]; }
    if (n.parent.hasOwnProperty('cX0')
        && n.parent.hasOwnProperty('cY0')) {
        return [n.parent.cX0, n.parent.cY0];
    }
    else if (n.parent.hasOwnProperty('parent')) {
        return getClosestAncestorCoord0(n.parent);
    }
}
*/

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

    // Compute the new visible nodes, determine the translation and zoom

    var visibleNodes = [];
    visibleNodes = visibleNodes.concat(curNode.parent || []);
    visibleNodes = visibleNodes.concat([curNode]);
    visibleNodes = visibleNodes.concat(curNode.children || []);

    visibleNodes = visibleNodes.concat(
        _(curNode.children || [])
        .map(function(n) { return (n.children || []); })
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

    var dX = maxX - minX;
    var dY = maxY - minY;

    xFactor = (dX == 0) ? width : (width / dX);
    yFactor = (dY == 0) ? height : (height / dY);

    canvas
        .transition()
        .duration(750)
        .attr("transform", "translate("
              + (margin.left - (((dX == 0) ? 0 : minX) * xFactor))
              + ", "
              + (margin.top  - (((dY == 0) ? 0 : minY) * yFactor))
              + ")")
    ;

    // New nodes need to be spawned at their parent's previous location,
    // stored in (cX0, cY0) at the end of this method

    var nodeEnter =
        node
        .enter()
        .append("g")
        .attr("class", "node")
        .attr("transform", function(d) {
            if (d.hasOwnProperty('parent')) {
                d.cX0 = d.parent.cX0;
                d.cY0 = d.parent.cY0;
            } else {
                // for the root, put it according to its (x0, y0)
                d.cX0 = d.x0 * xFactor;
                d.cY0 = d.y0 * yFactor;
            }
            return "translate(" + d.cX0 + "," + d.cY0 + ")";
        })
        .on("click", click)
    ;

    nodeEnter
        .append("text")
        .attr("font-family", "Monaco, DejaVu Sans Mono, monospace")
        .attr("font-size", "20")
        .style("text-anchor", "middle")
        .style("dominant-baseline", "middle")
        .text(function(d) {
            return d.name;
        })
    ;

    nodeEnter
        .insert("rect", ":first-child")
        .attr("x", function(){
            return this.nextSibling.getBBox().x - rectMargin.left;
        })
        .attr("y", function(){
            return this.nextSibling.getBBox().y - rectMargin.top;
        })
        .attr("width", function(n){
            var w = rectMargin.left
                + this.nextSibling.getBBox().width
                + rectMargin.right;
            n.width = w;
            return w;
        })
        .attr("height", function(n){
            var h = rectMargin.top
                + this.nextSibling.getBBox().height
                + rectMargin.bottom;
            n.height = h;
            return h;
        })
    ;

    // All the nodes need to move to their new position, according to the
    // new tree layout and the new zoom factors

    _(nodes)
        .each(function(n) {
            n.cX = n.x * xFactor;
            n.cY = n.y * yFactor;
        })
    ;

    node
        .transition()
        .duration(750)
        .attr("transform", function(d) {
            return "translate(" + d.cX + ", " + d.cY + ")";
        })
    ;

    canvas
        .selectAll("rect")
        .classed("tactic", function(d) { return isTactic(d); })
        .classed("goal", function(d) { return isGoal(d) && !d.solved; })
        .classed("solvedgoal", function(d) {
            return ( (isGoal(d) && d.solved)
                     || (isTactic(d) && d._children.length == 0)
                   );
        })
        .classed("current", function(d) {
            return d.id && (d.id == curNode.id);
        })
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
        .duration(750)
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
        .duration(750)
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
        .duration(750)
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

}

function contains(container, thing) { return (container.indexOf(thing) > -1); }

function nbDashes(s) {
    var n = s.match(/-/g);
    return (n || []).length;
}

function click(d) {

    navigateTo(d);

    if (!d._children || d._children.length == 0) {

        if (isGoal(d)) {
            syncQuery('Show.', function(response) {

                //console.log(response);

                d._children = _(response.nextGoals)
                    .map(mkTacticNode)
                    .value();

            });
        }
        // otherwise, this is a terminating tactic for this goal!
        else {
            solved(d.parent);
        }

    }

    expand(d);

    update(d);

/*
    // when the user clicks on a tactic node, bring them to the first goal
    if(isTactic(d) && d._children[0]) {
        click(d._children[0]);
    }
*/

}

function solved(goalNode) {
    goalNode.solved = true;

    collapse(goalNode);

    if (goalNode.hasOwnProperty('parent')) {
        navigateTo(goalNode.parent);

        // Bubble up if this was the last subgoal
        var lastSubgoal =
            _(goalNode.parent._children)
            .every(function(n) { return n.solved == true })
        ;

        if (lastSubgoal) {
            solved(goalNode.parent.parent);
        }
    }
}

function toggle(d) {
    if (d.children) {
        d.children = null;
    } else {
        d.children = d._children;
    }
}

function collapse(d) {
    if (d.children) {
        d.children = null;
    }
}

function collapseChildren(d) {
    _(d.children)
        .forEach(function(n) {
            collapse(n);
        })
    ;
}

function collapseExcept(d, e) {
    if (d.children) {
        d.children = [e];
    }
}

function expand(d) {
    d.children = d._children;
    if (isGoal(d)) {
        _(d.children)
            .each(function(c) {
                c.children = c._children;
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

function hasVisibleChild(n) { return (n.children && n.children[0]) ? true : false; }

function navigateTo(dest) {

    var a = commonAncestor(curNode, dest);

    var p = path(curNode, dest);

    var p1 = p;
    var p2 = _(p).rest().value();
    var q = _.zip(p1, p2);
    q.pop();

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
                    if(src._children.length == 0) {
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
