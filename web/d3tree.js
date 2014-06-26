
var i = 1; // unique identifier

var width = 1000;
var height = 320;
var margin = {top: 20, right: 20, bottom: 20, left: 20};
var rectMargin = {top: 2, right: 4, bottom: 2, left: 4};

var tree, svg, canvas;

var diagonal = d3.svg.diagonal();

var curNode = null;

var rootId = i++;

var root = null;

$(document).ready(function() {

    tree = d3.layout.tree()
        .size([width, height])
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
        .attr("class", "canvas")
        .attr("transform", "translate(" + margin.left + ", " + margin.top + ")")
    ;

    syncQuery('Abort All.', hIgnore);
    //syncQuery('Theorem plus_comm : ∀n m : nat, n + m = m + n.', hInit);
    syncQuery('Theorem plus_0_r : forall x, x + 0 = x.', hInit);
    syncQuery('Focus 1.', hLog);

/*
    curNode = root;

    update(root);

    click(root);
*/

});

function mkGoalNode(g, ndx) {
    return {
        "id": i++,
        "name": g.gGoal,
        "ndx": ndx + 1,
        "gid": g.gId,
    };
}

function mkTacticNode(t) {
    return {
        "id": i++,
        "name": t[0],
        "_children": _(t[1])
            .map(mkGoalNode)
            .value(),
    };
}

function hInit(response) {

    //console.log(response);

    // There should only be one goal at that point
    root = {
        "id": rootId,
        "name": response.currentGoals.focused[0].gGoal,
        "x0": width / 2,
        "y0": 0,
        "_children": _(response.nextGoals)
            .map(mkTacticNode)
            .value(),
    };

    curNode = root;

    update(root);

    click(root);

}

function nodeTransform(d) {
    return "translate(" + d.x + ", " + d.y + ")";
}

function linkDiagonal(d) {
    return diagonal(
        {
            "source": {"x": d.source.x, "y": d.source.y,},
            "target": {"x": d.target.x, "y": d.target.y,},
        }
    );
}

function update(source) {

    var nodes = tree.nodes(root);
    var links = tree.links(nodes);

    var node =
        canvas
        .selectAll("g.node")
        .data(nodes, function(d) {
            return d.id || (d.id = i++);
        });

    var link =
        canvas
        .selectAll("path")
        .data(links, function(d) {
            return d.id = d.source.id + "," + d.target.id;
        });

    var nodeEnter =
        node
        .enter()
        .append("g")
        .attr("class", "node")
        .attr("transform", function(d) {
            return "translate(" + source.x0 + "," + source.y0 + ")";
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
        .attr("width", function(){
            return rectMargin.left
                + this.nextSibling.getBBox().width
                + rectMargin.right;
        })
        .attr("height", function(){
            return rectMargin.top
                + this.nextSibling.getBBox().height
                + rectMargin.bottom;
        })
    ;

    node
        .transition()
        .duration(750)
        .attr("transform", nodeTransform)
    ;

    canvas
        .selectAll("rect")
        .classed("tactic", function(d) { return isTactic(d); })
        .classed("goal", function(d) { return isGoal(d) && !d.solved; })
        .classed("solvedgoal", function(d) { return isGoal(d) && d.solved; })
        .classed("current", function(d) {
            return d.id && (d.id == curNode.id);
        })
    ;

    nodeExit =
        node
        .exit()
        .transition()
        .duration(750)
        .attr("transform", function(d) {
            return "translate(" + d.parent.x + "," + d.parent.y + ")";
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
            var o = {x: source.x0, y: source.y0};
            return diagonal({source: o, target: o});
        })
    ;

    link
        .transition()
        .duration(750)
        .attr("d", linkDiagonal)
    ;

    link
        .exit()
        .transition()
        .duration(750)
        .attr("d", function(d) {
            var o = {x: d.source.x, y: d.source.y};
            return diagonal({source: o, target: o});
        })
        .style("opacity", "0")
        .remove()
    ;

    nodes.forEach(function(d) {
        d.x0 = d.x;
        d.y0 = d.y;
    });

}

function contains(container, thing) { return (container.indexOf(thing) > -1); }

function nbDashes(s) {
    var n = s.match(/-/g);
    return (n || []).length;
}

function click(d) {

    d.children = d._children;

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

    collapseChildren(d);

    expand(d);

    update(d);

    if(isTactic(d) && d._children[0]) {
        click(d._children[0]);
    }
}

function solved(goalNode) {
    goalNode.solved = true;
    collapse(goalNode);

    if (goalNode.parent) {
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
        //d._children = d.children;
        d.children = null;
    } else {
        d.children = d._children;
        //d._children = null;
    }
}

function collapse(d) {
    if (d.children) {
        //d._children = d.children;
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
        //d._children = d.children;
        d.children = [e];
    }
}

function expand(d) {
    if (!d.children) {
        d.children = d._children;
        //d._children = null;
    }
}

function commonAncestor(n1, n2) {
    if (n1.id == root.id || n2.id == root.id) { return root; }
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

function navigateTo(dest) {
    var a = commonAncestor(curNode, dest);
    var p = path(curNode, dest);
    var goingUp = true;
    _(p)
        .each(function(n) {
            if (n.depth == a.depth) {
                collapseChildren(n);
                goingUp = false;
            }
            else if (goingUp) {
                collapseChildren(n);
                if(isTactic(n)) {
                    // Apparently we need to Undo twice for subgoals solved
/*
                    if(n._children.length == 0) {
                        syncQuery('Undo.', hIgnore);
                    }
*/
                    syncQuery('Undo.', hLog);
                } else {
                    // 'Back.' does not work in -ideslave
                    // 'Back.' takes one step to undo 'Show.'
                    // 'Undo.' works in -ideslave
                    // 'Undo.' does not care about 'Show.' commands

                    if (n.solved) {
                        syncQuery('Undo.', hLog);
                    }

                    // Undo the 'Focus.' command
                    syncQuery('Undo.', hLog);
                }
            } else {
                // collapse tactic nodes of branches not taken
                if (isGoal(n.parent)) {
                    collapseExcept(n.parent, n);
                }

                if (isTactic(n)) {
                    syncQuery(n.name, hLog);
                } else {
                    syncQuery('Focus ' + n.ndx + '.', hLog);
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
    //console.log('Query: ' + q);
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
