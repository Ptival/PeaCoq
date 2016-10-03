import * as d3Hierarchy from "d3-hierarchy"
import { GoalNode } from "./goalnode"
import { TacticGroupNode } from "./tacticgroupnode"
import * as ProofTreeUtils from "./utils"

/*
 * Returns a rect of the absolute position of [elmt] within the canvas. It needs
 * [node] in order to return absolute values, where [node] is the node element
 * within which [elmt] lives.
 */
function elmtRect(node: ProofTreeTypes.Node, elmt: HTMLElement) {
  const rect = elmt.getBoundingClientRect()
  const containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect()
  const left = getDestinationScaledX(node) + ProofTreeUtils.deltaX(containerRect, rect)
  const top = getDestinationScaledY(node) + ProofTreeUtils.deltaY(containerRect, rect)
  return {
    "left": left, "right": left + rect.width, "width": rect.width,
    "top": top, "bottom": top + rect.height, "height": rect.height,
  }
}

export function getDestinationScaledX(node: ProofTreeTypes.Node): number {
  const tree = node.data.proofTree
  return ProofTreeUtils.nodeX(node) * tree.xFactor + xOffset(node)
}

export function getDestinationScaledY(node: ProofTreeTypes.Node): number {
  const tree = node.data.proofTree
  return ProofTreeUtils.nodeY(node) * tree.yFactor + yOffset(node)
}

export function getHierarchyGoalAncestor(d: ProofTreeTypes.Node): Maybe<ProofTreeTypes.Node> {
  if (d.parent === null) { return nothing<ProofTreeTypes.Node>() }
  if (isGoalNodeHierarchyNode(d.parent)) { return just(d.parent) }
  return getHierarchyGoalAncestor(d.parent)
}

function isGoalNodeHierarchyNode(d: d3Hierarchy.HierarchyNode<IProofTreeNode>): d is d3Hierarchy.HierarchyNode<IGoalNode> {
  return d.data instanceof GoalNode
}

function getHierarchyFocusedChild(d: ProofTreeTypes.Node): Maybe<ProofTreeTypes.Node> {
  throw "TODO"
}

function xOffset(d: ProofTreeTypes.Node): number {
  return - d.data.getWidth() / 2 // position the center
}

function isCurGoalChild(n: ProofTreeTypes.Node): boolean {
  return (
    n.parent !== null
    && n.parent.data.isCurNode()
  )
}

function isCurGoalGrandChild(n: ProofTreeTypes.Node): boolean {
  return (
    n.parent !== null
    && n.parent.parent !== null
    && n.parent.parent.data.isCurNode()
  )
}

function getFocusedChild(n: ProofTreeTypes.Node): Maybe<ProofTreeTypes.Node> {
  // const node = n.data
  return n.data.getFocusedChild().caseOf({
    nothing: () => nothing<ProofTreeTypes.Node>(),
    just: (focusedChild: IProofTreeNode) => {
      const children = n.children
      if (children === undefined) { return thisShouldNotHappen() }
      const found = children.find(c => c.data.id === focusedChild.id)
      if (found === undefined) { return thisShouldNotHappen() }
      return just(found)
    }
  })
}

function isCurNodeParent(d: ProofTreeTypes.Node): boolean {
  const curNode = d.data.proofTree.getHierarchyCurNode()
  return (
    d.parent !== null
    && d.parent.data.id === curNode.data.id
  )
}

function yOffset(d: ProofTreeTypes.Node): number {
  const tree = d.data.proofTree
  const offset = - d.data.getHeight() / 2 // for the center
  const focusedChild = getFocusedChild(d)

  // all tactic nodes are shifted such that the current tactic is centered
  // assert(isGoal(tree.curNode), "yOffset assumes the current node is a goal!")
  if (isCurGoalChild(d)) {
    const parent = d.parent
    if (parent === null) { return thisShouldNotHappen() }
    // assert(focusedChild !== undefined, "yOffset: focusedChild === undefined")
    return offset + (
      ProofTreeUtils.nodeY(parent) - ProofTreeUtils.nodeY(fromJust(focusedChild))
    ) * tree.yFactor
  }

  // all goal grandchildren are shifted such that the context line of the
  // current goal and the current suboal align
  if (isCurGoalGrandChild(d)) {
    return offset + tree.descendantsOffset
  }

  // we center the curNode parent to its focused child
  if (isCurNodeParent(d)) {
    if (d.data instanceof TacticGroupNode) {
      return offset + (
        ProofTreeUtils.nodeY(tree.getHierarchyCurNode()) - ProofTreeUtils.nodeY(d)
      ) * tree.yFactor
    } else {
      // tree should not happen anymore (should not be a GoalNode)
      debugger
    }
  }

  // the other nodes (current goal and its ancestors) stay where they need
  return offset
}
