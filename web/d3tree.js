
/*** TODO ***/

// CONFIGURATION
var nodeMinSpacing = 5;
var nodeStroke = 2;
var nodeHeight = 25;
var rectMargin = {top: 2, right: 8, bottom: 2, left: 8};
var scrollbarWidth = 20; // I could compute this if I cared enough
var nbChildrenToShow = 2;
var animationDuration = 420;

// OTHER GLOBALS
var maxNodesOnLine = Math.pow(nbChildrenToShow, 2);
var diagonal = d3.svg.diagonal();
var rootId = _.uniqueId();
var animationRunning = false;
var thmNdx = 0;

// GLOBALS TO BE INITIALIZED LATER
var tree, svg, canvas, context, tactics;
var smallestNodeWidth, bigNodeWidth, width, height, curNode, rootNode;
var xFactor, yFactor;

// These tactic sets each build on top of the previous one
var tSet = ['simpl', 'reflexivity', 'intro', 'rewrite', 'destruct', 'induction'];
var tReflexivity = tSet.slice(0, 2);
var tIntro       = tSet.slice(0, 3);
var tRewrite     = tSet.slice(0, 4);
var tDestruct    = tSet.slice(0, 5);
var tInduction   = tSet.slice(0, 6);
// These ones are more special
var tCompute = tReflexivity.concat(['compute']);

var thms = [
['Theorem branching : ∀(a b : comparison), a = Eq → b = Eq → a = b.', tDestruct],
['Theorem plus_O_n : ∀n : nat, 0 + n = n.', tIntro],
['Theorem plus_1_l : ∀n : nat, 1 + n = S n.', tIntro],
['Theorem mult_0_l : ∀n : nat, 0 * n = 0.', tIntro],
['Theorem plus_id_example : ∀n m:nat, n = m → n + n = m + m.', tRewrite],
['Theorem plus_id_exercise : ∀n m o : nat, n = m → m = o → n + m = m + o.', tRewrite],
['Theorem mult_0_plus : ∀n m : nat, (0 + n) * m = n * m.', tRewrite],
['Theorem mult_S_1 : ∀n m : nat, m = S n → m * (1 + n) = m * m.', tRewrite],
['Theorem negb_involutive : ∀b : bool, negb (negb b) = b.', tDestruct],
['Theorem identity_fn_applied_twice : ∀(f : bool → bool), (∀(x : bool), f x = x) → ∀(b : bool), f (f b) = b.', tDestruct],
['Theorem andb_eq_orb : ∀(b c : bool), (andb b c = orb b c) → b = c.', tDestruct.concat(['admit'])],
['Theorem andb_true_elim1 : ∀b c : bool, andb b c = true → b = true.', tDestruct],
['Theorem andb_true_elim2 : ∀b c : bool, andb b c = true → c = true.', tDestruct],
['Theorem plus_0_r : ∀n:nat, n + 0 = n.', tDestruct],
['Theorem minus_diag : ∀n, minus n n = 0.', tDestruct],
['Theorem mult_0_r : ∀n:nat, n * 0 = 0.', tDestruct],
['Theorem plus_n_Sm : ∀n m : nat, S (n + m) = n + (S m).', tInduction],
['Theorem plus_comm : ∀n m : nat, n + m = m + n.', tInduction],
['Theorem plus_assoc : ∀n m p : nat, n + (m + p) = (n + m) + p.', tInduction],
['Theorem plus_rearrange : ∀n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).', tInduction],
['Theorem plus_swap : ∀n m p : nat, n + (m + p) = m + (n + p).', tInduction],
['Theorem mult_comm : ∀m n : nat, m * n = n * m.', tInduction],
['Theorem andb_false_r : ∀b : bool, andb b false = false.', tInduction],
['Theorem mult_1_l : ∀n:nat, 1 * n = n.', tInduction],
['Theorem all3_spec : ∀b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.', tInduction],
['Theorem mult_plus_distr_r : ∀n m p : nat, (n + m) * p = (n * p) + (m * p).', tInduction],
['Theorem mult_assoc : ∀n m p : nat, n * (m * p) = (n * m) * p.', tInduction],
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
    //return smallestNodeWidth;
    return (isCurNode(d) || isCurNodeParent(d))
        ? (
            (
                $(window).width()
                    - scrollbarWidth
                    - (2 * nodeMinSpacing)
            ) / 3
        )
        : smallestNodeWidth
    ;
}

function treeDepth(root) {
    return (
        root.visibleChildren
            ? 1 + _(root.visibleChildren).map(treeDepth).max()
            : 0
    );
}

function addTheorem(t) {
    var b = $('<button>', {
        text: t[0],
        click: function() { newTheorem(t); }
    });
    $('#buttons').append(b);
}

$(document).ready(function() {

    _(thms).each(addTheorem);

    smallestNodeWidth = evenFloor(
        ($(window).width()
         - scrollbarWidth
         - ((maxNodesOnLine - 1) * nodeMinSpacing)
        ) / maxNodesOnLine
    );

    bigNodeWidth = evenFloor (
        ($(window).width()
         - scrollbarWidth
         - (2 * nodeMinSpacing)
        ) / 3
    );

    width =
        maxNodesOnLine * smallestNodeWidth
        + (maxNodesOnLine - 1) * nodeMinSpacing;
    height = $(window).height();
    xFactor = width;
    yFactor = height;

    newTheorem(thms[thmNdx]);

});

function newTheorem(thmTac) {

    var theorem = thmTac[0];
    tactics = thmTac[1];

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
            if (animationRunning) {
                // all keys are frozen during animation
                d3.event.preventDefault();
                return;
            }
            switch (d3.event.keyCode) {

            case 37: case 65: // Left, a
                shiftLeft(curNode);
                break;

            case 39: case 68: // Right, d
                shiftRight(curNode);
                break;

            case 38: case 87: // Up, w
                if(hasParent(curNode)) {
                    click(curNode.parent);
                }
                break;

            case 40: case 83: // Down, s
                if (isTactic(curNode)) {
                    var dest = _(curNode.visibleChildren).find(function(n) {
                        return !(n.solved);
                    });
                    if (dest) { click(dest); }
                } else {
                    if (curNode.visibleChildren[0]) {
                        click(curNode.visibleChildren[0]);
                    }
                }
                break;

            case 49: case 97: // 1, K1
                if (curNode.visibleChildren.length > 0) {
                    click(curNode.visibleChildren[0]);
                }
                break;

            case 50: case 98: // 2, K2
                if (curNode.visibleChildren.length > 1) {
                    click(curNode.visibleChildren[1]);
                }
                break;

            case 51: case 99: // 3, K3
                if (curNode.visibleChildren.length > 2) {
                    click(curNode.visibleChildren[2]);
                }
                break;

            default: return;
            }
            // if we haven't returned, we don't want the normal key behavior
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

    var contextDivWidth = bigNodeWidth - rectMargin.left - rectMargin.right;
    var contextHeight;

    context
        .append("foreignObject")
        .attr('x', rectMargin.left)
        .attr("width", contextDivWidth)
        .append("xhtml:body")
        .html('<div><p>Empty context</p></div>')
    // now retrieve the computed height of the div
        .attr("height", function() {
            contextHeight = this.firstChild.getBoundingClientRect().height
            return contextHeight;
        })
    ;

    context
        .insert("rect", ":first-child")
        .attr("width", bigNodeWidth)
        .attr("height", contextHeight)
    ;

    debug =
        svg
        .append("g")
        .attr("class", "debug")
    ;

    var debugWidth = bigNodeWidth - rectMargin.left - rectMargin.right;
    var debugHeight;

    debug
        .append("foreignObject")
        .attr('x', width - bigNodeWidth + rectMargin.left)
        .attr("width", bigNodeWidth - rectMargin.left - rectMargin.right)
        .append("xhtml:body")
        .html('<div><p>No debug information</p></div>')
        .attr("height", function() {
            debugHeight = this.firstChild.getBoundingClientRect().height
            return debugHeight;
        })
    ;

    debug
        .insert("rect", ":first-child")
        .attr("x", width - bigNodeWidth)
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

function tryAllTactics() {

    var res = [];
    var unfocusedBefore;

    syncQueryUndo('idtac.', function(response) {
        unfocusedBefore = response.rGoals.unfocused;
        res.push(mkTacticNode('idtac.', response.rGoals.focused));
    });

    var run = function(t) {
        syncQueryUndo(t + '.', function(response) {

            if(response.rResponse.tag === "Good") {
                if (_.isEqual(response.rGoals.unfocused, unfocusedBefore)) {
                    res.push(mkTacticNode(t + '.', response.rGoals.focused));
                } else {
                    res.push(mkTacticNode(t + '.', []));
                }
            }

/*
            else {
                console.log('Bad response for tactic ' + t + ': ', response);
            }
*/

        });
    }

    var curHyps = [];
    if (curNode !== undefined) {
        var curGoal = (isGoal(curNode)) ? curNode : curNode.parent;
        curHyps = curGoal.hyps;
    }

    _(tactics).each(function(t) {
        switch (t) {
        case "destruct":
            _(curHyps).each(function(n) {
                run('destruct ' + hypName(n));
            });
            break;
        case "induction":
            _(curHyps).each(function(n) {
                run('induction ' + hypName(n));
            });
            break;
        case "intro":
            run('intro');
            run('intros');
            break;
        case "rewrite":
            _(curHyps).each(function(n) {
                run('rewrite -> ' + hypName(n));
                run('rewrite <- ' + hypName(n));
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

function hInit(response) {

    // There should only be one goal at that point
    rootNode = {
        "id": rootId,
        "name": response.rGoals.focused[0].gGoal,
        "x0": 0.5,
        "y0": 0,
        "allChildren": tryAllTactics(),
        "ndx": 1,
        "depth": 0, // need to set depth for isGoal() to work early
        "offset": 0,
        "hyps": [],
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

function isCurNodeSibling(n) {
    return (!isCurNode(n) && hasParent(n) && isCurNodeParent(n.parent));
}

function hypName(h) {
    return h.slice(0, h.indexOf(':') - 1);
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
            return d.id || (d.id = _.uniqueId());
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

    var fo =
        gs
        .append("foreignObject")
        .attr("width", function(d) {
            return nodeWidth(d) - rectMargin.left - rectMargin.right;
        })
    ;

    fo
        .append("xhtml:body")
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
                                return hypName(h0) === hypName(h);
                            });

                        if (previousH === undefined) {
                            added.push(h);
                        } else {
                            if (previousH !== h) {
                                changed.push({"before": previousH, "after": h});
                            }
                            gpHyps.pull(previousH);
                        }

                    });

                    removed = gpHyps.value();

                    _(removed).each(function(h) {
                        jQDiv.append($("<span>").addClass("removed").text('⊖ ' + h));
                        jQDiv.append($("<br>"));
                    });

                    var fo = d3.select(this);

                    _(changed).each(function(hs) {

                        fo
                            .select("div")
                            .append("span")
                            .text(hs.after)
                            .attr("class", "changed")
                            .on("mouseover", function() {
                                d3.select(this)
                                    .attr("class", "removed").text(hs.before);
                            })
                            .on("mouseout", function(d) {
                                d3.select(this)
                                    .attr("class", "changed").text(hs.after);
                            })
                        ;

                        fo.select("div").append("br");

                    });

                    _(added).each(function(h) {
                        jQDiv.append($("<span>").addClass("added").text('⊕ ' + h));
                        jQDiv.append($("<br>"));
                    });

                    jQDiv.append($('<hr>'));

                } else {

                    _(d.hyps).each(function(h) {
                        jQDiv.append($("<span>").addClass("added").text('⊕ ' + h));
                    });

                    if (!_(d.hyps).isEmpty()) { jQDiv.append($('<hr>')); }

                }

            }

            jQDiv
                .append($("<span>").text(d.name))
            ;

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
            if (isCurNodeChild(n) || isCurNodeGrandChild(n)) {
                n.cX = (n.x + descendantsXOffset) * xFactor;
            } else if (isCurNodeSibling(n)) {
                var smallBigDelta = bigNodeWidth - smallestNodeWidth;
                if (n.ndx < curNode.ndx) {
                    n.cX = n.x * xFactor - smallBigDelta / 2;
                } else {
                    n.cX = n.x * xFactor + smallBigDelta / 2;
                }
            } else if (isCurNodeParent(n)) {
                n.cX = curNode.x * xFactor;
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

    if (d.solved) {
        if (hasParent(d)) {
            click(d.parent);
        }
        return;
    }

    navigateTo(d);

    if (!d.hasOwnProperty('allChildren') || d.allChildren.length === 0) {
        if (isGoal(d)) {
            d.allChildren = tryAllTactics();
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
    n.allChildren = [];
    collapse(n);
    if (hasParent(n)) {
        navigateTo(n.parent);
        animationRunning = true;
        window.setTimeout(function () {
            childSolved(n.parent);
            update(n.parent);
            animationRunning = false;
        }, animationDuration);
    } else {
        // This goal is solved, let's try to solve the next one!
        thmNdx++;
        window.setTimeout(function() { newTheorem(thms[thmNdx]); }, animationDuration);
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
            .every(function(n) { return n.solved === true; })
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
                    // need to Undo as many times as the focus depth difference
                    // between before and after the terminating tactic + 1
                    if(src.terminating) {
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

function syncRequest(r, q, h) {
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: false,
        success: function(response) {
            //console.log('response', response);
            if (r === 'query') { updateDebug(response); }
            h(response);
        }
    });
}

function syncQuery(q, h) { syncRequest('query', q, h); }
function syncQueryUndo(q, h) { syncRequest('queryundo', q, h); }

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
    if (response.rGoals.focused.length > 0) {
        debugDiv.html(response.rGoals.focused[0].gGoal);
    } else {
        debugDiv.html(response.rResponse.contents[0]);
    }

    updateNodeHeight(debug);

}
