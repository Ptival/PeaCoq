/*
  Stuff that is somewhat general but mostly useful for the proof tree.
 */

function computeGoalWidth(width) {
  let goalShare = 15 / 20;
  return Math.floor(width * (goalShare / 2));
}

function computeTacticWidth(width) {
  let tacticShare = 4 / 20;
  return Math.floor(width * (tacticShare / 2));
}

/*
 * Returns a rect of the absolute position of [elmt] within the canvas. It needs
 * [node] in order to return absolute values, where [node] is the node element
 * within which [elmt] lives.
 */
function elmtRect(node, elmt) {
  let rect = elmt.getBoundingClientRect();
  let containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect();
  let left = node.cX + deltaX(containerRect, rect);
  let top = node.cY + deltaY(containerRect, rect);
  return {
    "left": left, "right": left + rect.width, "width": rect.width,
    "top": top, "bottom": top + rect.height, "height": rect.height,
  };
}

function elmtRect0(node, elmt) {
  let rect = elmt.getBoundingClientRect();
  let containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect();
  let left = node.cX0 + deltaX(containerRect, rect);
  let top = node.cY0 + deltaY(containerRect, rect);
  return {
    "left": left, "right": left + rect.width, "width": rect.width,
    "top": top, "bottom": top + rect.height, "height": rect.height,
  };
}

type Rectangle = {
  bottom: number;
  left: number;
  right: number;
  top: number;
}

function deltaX(rect1: Rectangle, rect2: Rectangle): number {
  return rect2.left - rect1.left;
}
function deltaY(rect1: Rectangle, rect2: Rectangle): number {
  return rect2.top - rect1.top;
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

function makeContextDivider() {
  return $("<hr>")
    // inlining the CSS for svg_datatourl
    .css("border", 0)
    .css("border-top", "1px solid black")
    .css("margin", 0)
    ;
}

type XY = { x: number; y: number; }
function swapXY(r: any): any {
  return { "x": r.y, "y": r.x };
}

function hasParent(n) {
  return n.parent !== undefined;
}

function hasGrandParent(n) {
  return hasParent(n) && hasParent(n.parent);
}

function byNodeId(d) { return d.id; }
function byLinkId(d) { return d.source.id + "," + d.target.id; }

// transposition accessors
function nodeX(d) { return d.y; }
function nodeY(d) { return d.x; }

function getClosestGoal(node: ProofTreeNode): GoalNode {
  if (node instanceof GoalNode) { return node; }
  // if it is not a goal, it ought to have a parent
  if (node instanceof TacticGroupNode) {
    assert(node.parent instanceof GoalNode, "getClosestGoal");
    return <GoalNode>node.parent;
  }
  throw node;
}
function goalNodeUnicityRepr(node: GoalNode): string {
  throw ("TOREDO");
  /*
  retur  JSON.stringify({
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
  */
}

function tacticUnicityRepr(node: Tactic): string {
  return JSON.stringify(
    _(node.goals)
      .map(goalNodeUnicityRepr)
      .value()
  );
}

let centerLeftOffset = +10;

let centerRightOffset = -10;

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

/*
  This might be terrible design, but [spotTheDifference] currently marks inline
  diffs through CSS background-color. It's much more stable than using
  rectangles when animated.
 */
function spotTheDifferences(before, after) {

  function rec(before, after) {

    let nbBefore = before.children().length;
    let nbAfter = after.children().length;
    if (nbBefore !== nbAfter) {
      return [{
        "removed": before,
        "added": after,
      }];
    }

    let nbChildren = nbBefore;
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

    let everyChildChanged = true;

    let childrenChanges = _.range(nbChildren).reduce(function(acc, i) {
      let tmp = rec($(before.children()[i]), $(after.children()[i]));
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

  let removed = [];
  let added = [];

  _(rec($(before).children(), $(after).children())).each(function(pair, ndx) {
    pair.removed.css("background-color", diffColor(ndx));
    pair.added.css("background-color", diffColor(ndx));
    //removed.push(pair.removed);
    //added.push(pair.added);
  });

  return { "removed": removed, "added": added };
}
