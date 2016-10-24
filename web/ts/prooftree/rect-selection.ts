import * as d3Interpolate from "d3-interpolate"
import { GoalNode } from "./goalnode"
import * as HierarchyNodeUtils from "./hierarchy-node-utils"
import { TacticGroupNode } from "./tacticgroupnode"

export function onRectEnter(s: ProofTreeTypes.NodeSelection): void {
  s
    .append("rect")
    .classed("goal", d => d.data instanceof GoalNode)
    .classed("tactic", d => d.data instanceof TacticGroupNode)
    .attr("x", d => d.data.currentScaledX)
    .attr("y", d => d.data.currentScaledY)
    .attr("width", d => d.data.getWidth())
    .attr("height", d => d.data.getHeight())
    .attr("rx", d => d.data instanceof GoalNode ? 0 : 10)
  // .style("opacity", 0)
}

export function onRectExit(s: ProofTreeTypes.NodeSelection): void {
  s.transition()
    .attr("x", d =>
      HierarchyNodeUtils.getHierarchyGoalAncestor(d).caseOf({
        nothing: () => HierarchyNodeUtils.getDestinationScaledX(d),
        just: gp => HierarchyNodeUtils.getDestinationScaledX(gp),
      })
    )
    .attr("y", d =>
      HierarchyNodeUtils.getHierarchyGoalAncestor(d).caseOf({
        nothing: () => HierarchyNodeUtils.getDestinationScaledY(d),
        just: gp => HierarchyNodeUtils.getDestinationScaledY(gp),
      })
    )
    // .style("opacity", "0")
    .remove()
}

export function onRectUpdatePostMerge(s: ProofTreeTypes.NodeSelection): void {
  s
    .classed("currentnode", d => d.data.proofTree.isCurNode(d.data))
    .classed("solved", d => d.data.isSolved())
    .transition()
    .attr("width", d => d.data.getWidth())
    .attr("height", d => d.data.getHeight())
    .attrTween("x", (d, i, a) => {
      const interpolator = d3Interpolate.interpolateRound(d.data.currentScaledX, HierarchyNodeUtils.getDestinationScaledX(d))
      return t => {
        d.data.currentScaledX = interpolator(t)
        return `${d.data.currentScaledX}`
      }
    })
    .attrTween("y", (d, i, a) => {
      const interpolator = d3Interpolate.interpolateRound(d.data.currentScaledY, HierarchyNodeUtils.getDestinationScaledY(d))
      return t => {
        d.data.currentScaledY = interpolator(t)
        return `${d.data.currentScaledY}`
      }
    })
  // .attr("y", d => d.getDestinationScaledY())
  // .style("opacity", 1)
}
