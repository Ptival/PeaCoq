import * as d3Hierarchy from "d3-hierarchy"
import * as d3Path from "d3-path"
import * as d3Scale from "d3-scale"
import * as HierarchyNodeUtils from "./hierarchy-node-utils"

/*
  Stuff that is somewhat general but mostly useful for the proof tree.
 */

// function elmtRect0(node: IProofTreeNode, elmt: HTMLElement) {
//   const rect = elmt.getBoundingClientRect()
//   const containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect()
//   const left = node.cX0 + deltaX(containerRect, rect)
//   const top = node.cY0 + deltaY(containerRect, rect)
//   return {
//     "left": left, "right": left + rect.width, "width": rect.width,
//     "top": top, "bottom": top + rect.height, "height": rect.height,
//   }
// }

type Rectangle = {
  bottom: number
  left: number
  right: number
  top: number
}

export function deltaX(rect1: Rectangle, rect2: Rectangle): number {
  return rect2.left - rect1.left
}
export function deltaY(rect1: Rectangle, rect2: Rectangle): number {
  return rect2.top - rect1.top
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
}

export function swapXY({ x, y }: XY): XY {
  return { x: y, y: x }
}

// transposition accessors
export function nodeX(d: ProofTreeTypes.Node): number {
  return d.y
}

export function nodeY(d: ProofTreeTypes.Node): number {
  return d.x
}

// function goalNodeUnicityRepr(node: IGoalNode): string {
//   debugger
//   /*
//   retur  JSON.stringify({
//     "goalTerm": node.goalTerm,
//     "hyps": _(node.hyps)
//       .map(function(h) {
//         return {
//           "hName": h.hName,
//           "hValue": h.hValue,
//           "hType": h.hType,
//         }
//       })
//       .value(),
//   })
//   */
// }

// function tacticUnicityRepr(node: ITactic): string {
//   return JSON.stringify(
//     _(node.goals)
//       .map(goalNodeUnicityRepr)
//       .value()
//   )
// }

const centerLeftOffset = +10

const centerRightOffset = -10

function mkCenterLeft(x: number, y: number, h: number): XY {
  return { x: x + centerLeftOffset, y: y + h / 2 }
}

export function currentCenterLeft(d: ProofTreeTypes.Node): XY {
  return mkCenterLeft(d.data.currentScaledX, d.data.currentScaledY, d.data.getHeight())
}

export function destinationCenterLeft(d: ProofTreeTypes.Node): XY {
  return mkCenterLeft(HierarchyNodeUtils.getDestinationScaledX(d), HierarchyNodeUtils.getDestinationScaledY(d), d.data.getHeight())
}

function mkCenterRight(x: number, y: number, w: number, h: number): XY {
  return { x: x + w + centerRightOffset, y: y + h / 2 }
}

export function currentCenterRight(d: ProofTreeTypes.Node): XY {
  return mkCenterRight(d.data.currentScaledX, d.data.currentScaledY, d.data.getWidth(), d.data.getHeight())
}

export function destinationCenterRight(d: ProofTreeTypes.Node): XY {
  return mkCenterRight(HierarchyNodeUtils.getDestinationScaledX(d), HierarchyNodeUtils.getDestinationScaledY(d), d.data.getWidth(), d.data.getHeight())
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
//     const nbBefore = before.children().length
//     const nbAfter = after.children().length
//     if (nbBefore !== nbAfter) {
//       return [{
//         "removed": before,
//         "added": after,
//       }]
//     }
//
//     const nbChildren = nbBefore
//     if (nbChildren === 0) { // both leaves
//       if (before.html() !== after.html()) {
//         return [{
//           "removed": before,
//           "added": after,
//         }]
//       } else {
//         return [];
//       }
//     }
//
//     const everyChildChanged = true
//
//     const childrenChanges = _.range(nbChildren).reduce(function(acc, i) {
//       const tmp = rec($(before.children()[i]), $(after.children()[i]))
//       if (tmp.length === 0) { everyChildChanged = false; }
//       return acc.concat(tmp)
//     }, [])
//       
//
//     if (everyChildChanged) {
//       return [{
//         "removed": before,
//         "added": after,
//       }]
//     } else {
//       return childrenChanges
//     }
//
//   }
//
//   const removed = []
//   const added = []
//
//   _(rec($(before).children(), $(after).children())).each(function(pair, ndx) {
//     pair.removed.css("background-color", diffColor(ndx))
//     pair.added.css("background-color", diffColor(ndx))
//     //removed.push(pair.removed)
//     //added.push(pair.added)
//   })
//
//   return { "removed": removed, "added": added }
// }

/*
  creates an empty rectangle in the same column as [node], at vertical position
  [currentY]
*/
function destinationEmptyRect(node: ProofTreeTypes.Node, currentY: number): Rectangle {
  const delta = 1 // how big to make the empty rectangle
  return $.extend(
    {
      "left": HierarchyNodeUtils.getDestinationScaledX(node),
      "right": HierarchyNodeUtils.getDestinationScaledX(node) + node.data.getWidth(),
      "width": node.data.getWidth()
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
  )
}

function currentEmptyRect(node: IProofTreeNode, currentY: number): Rectangle {
  const delta = 1 // how big to make the empty rectangle
  return $.extend(
    {
      "left": node.currentScaledX,
      "right": node.currentScaledY + node.getWidth(),
      "width": node.getWidth()
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
  )
}

const diffColor = (() => {
  const colors = [
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
  ]
  return d3Scale.scaleOrdinal<number, string>(colors)
})()

function mkDiagonal(
  cL: (xy: XY) => XY,
  cR: (xy: XY) => XY
): (d: ProofTreeTypes.Link) => string {
  return d => {
    const srcNode = d.source
    const tgtNode = d.target
    const src = swapXY(cR(srcNode))
    const tgt = swapXY(cL(tgtNode))
    const path = d3Path.path()
    path.moveTo(src.x, src.y)
    const midX = Math.floor((src.x + tgt.x) / 2)
    // const midY = Math.floor((src.y + tgt.y) / 2)
    path.bezierCurveTo(midX, src.y, midX, tgt.y, tgt.x, tgt.y)
    return path.toString()
  }
}

export const currentDiagonal = mkDiagonal(currentCenterLeft, currentCenterRight)
export const destinationDiagonal = mkDiagonal(destinationCenterLeft, destinationCenterRight)

export function makeTreeFromHierarchy(hierarchyRoot: d3Hierarchy.HierarchyNode<IProofTreeNode>): d3Hierarchy.HierarchyPointNode<IProofTreeNode> {
  return d3Hierarchy.tree<IProofTreeNode>()
    .separation(d => {
      // TODO: now that I put fake nodes, still need this?
      // TODO: this just won't work, need invisible children
      // for tactics without children
      return 1 / (1 + Math.pow(d.depth, 3))
    })
    (hierarchyRoot)
}
