import { GoalNode } from "./goalnode";
import { ProofTree, proofTrees } from "./prooftree";
import { ProofTreeNode } from "./prooftreenode";
import { Tactic } from "./tactic";

/*
  Stuff that is somewhat general but mostly useful for the proof tree.
 */

export function getActiveProofTree(): Maybe<ProofTree> {
  return (
    proofTrees.length > 0
      ? just(proofTrees[0])
      : nothing()
  );
}

type Hypothesis = {
  div: HTMLElement;
  hName: string;
  hValue: string;
  hType: string;
}

export type ProofTreeLink = d3.svg.diagonal.Link<ProofTreeNode>;

export type TacticGroup = {
  name: string;
  tactics: string[];
}

export type WorklistItem = () => Promise<TacticGroup[]>;

/*
 * Returns a rect of the absolute position of [elmt] within the canvas. It needs
 * [node] in order to return absolute values, where [node] is the node element
 * within which [elmt] lives.
 */
function elmtRect(node, elmt) {
  let rect = elmt.getBoundingClientRect();
  let containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect();
  let left = node.getScaledX() + deltaX(containerRect, rect);
  let top = node.getScaledY() + deltaY(containerRect, rect);
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

type XY = { x: number; y: number; }

export function swapXY(r: XY): XY {
  let [x, y] = [r.x, r.y];
  r.x = y;
  r.y = x;
  return r;
}

export function byNodeId(d: ProofTreeNode): string { return d.id; }
export function byLinkId(d: ProofTreeLink): string { return d.source.id + "," + d.target.id; }

// transposition accessors
export function nodeX(d: ProofTreeNode): number {
  if (d === undefined) {
    throw "nodeX";
  }
  return d.y;
}

export function nodeY(d: ProofTreeNode): number {
  if (d === undefined) {
    throw "nodeY";
  }
  return d.x;
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

export function centerLeft0(d: ProofTreeNode): XY {
  return {
    "x": d.getOriginalScaledX() + centerLeftOffset,
    "y": d.getOriginalScaledY() + d.getHeight() / 2,
  };
}

export function centerRight0(d: ProofTreeNode): XY {
  return {
    "x": d.getOriginalScaledX() + d.getWidth() + centerRightOffset,
    "y": d.getOriginalScaledY() + d.getHeight() / 2,
  };
}

export function centerLeft(d: ProofTreeNode): XY {
  return {
    "x": d.getScaledX() + centerLeftOffset,
    "y": d.getScaledY() + d.getHeight() / 2,
  };
}

export function centerRight(d: ProofTreeNode): XY {
  return {
    "x": d.getScaledX() + d.getWidth() + centerRightOffset,
    "y": d.getScaledY() + d.getHeight() / 2,
  };
}

/*
Right now this code doesn't make sense anymore, even type-wise the last
lines return an object of lists. Disabled for now.
*/

/*
  This might be terrible design, but [spotTheDifference] currently marks inline
  diffs through CSS background-color. It's much more stable than using
  rectangles when animated.
 */
// function spotTheDifferences(before: JQuery, after: JQuery) {
//
//   function rec(before, after) {
//
//     let nbBefore = before.children().length;
//     let nbAfter = after.children().length;
//     if (nbBefore !== nbAfter) {
//       return [{
//         "removed": before,
//         "added": after,
//       }];
//     }
//
//     let nbChildren = nbBefore;
//     if (nbChildren === 0) { // both leaves
//       if (before.html() !== after.html()) {
//         return [{
//           "removed": before,
//           "added": after,
//         }];
//       } else {
//         return [];;
//       }
//     }
//
//     let everyChildChanged = true;
//
//     let childrenChanges = _.range(nbChildren).reduce(function(acc, i) {
//       let tmp = rec($(before.children()[i]), $(after.children()[i]));
//       if (tmp.length === 0) { everyChildChanged = false; }
//       return acc.concat(tmp);
//     }, [])
//       ;
//
//     if (everyChildChanged) {
//       return [{
//         "removed": before,
//         "added": after,
//       }];
//     } else {
//       return childrenChanges;
//     }
//
//   }
//
//   let removed = [];
//   let added = [];
//
//   _(rec($(before).children(), $(after).children())).each(function(pair, ndx) {
//     pair.removed.css("background-color", diffColor(ndx));
//     pair.added.css("background-color", diffColor(ndx));
//     //removed.push(pair.removed);
//     //added.push(pair.added);
//   });
//
//   return { "removed": removed, "added": added };
// }

/*
  creates an empty rectangle in the same column as [node], at vertical position
  [currentY]
*/
function emptyRect(node: ProofTreeNode, currentY: number): Rectangle {
  let delta = 1; // how big to make the empty rectangle
  return $.extend(
    {
      "left": node.getScaledX(),
      "right": node.getScaledX() + node.getWidth(),
      "width": node.getWidth()
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
  );
}

function emptyRect0(node: ProofTreeNode, currentY: number): Rectangle {
  let delta = 1; // how big to make the empty rectangle
  return $.extend(
    {
      "left": node.getOriginalScaledX(),
      "right": node.getOriginalScaledY() + node.getWidth(),
      "width": node.getWidth()
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
  );
}
