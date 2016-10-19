import * as d3Selection from "d3-selection"
import * as HierarchyNodeUtils from "./hierarchy-node-utils"
import * as ProofTreeUtils from "./utils"

export function onLinkEnter(s: ProofTreeTypes.LinkSelection): void {
    s.append("path")
      .classed("link", true)
      .attr("fill", "none")
      .attr("d", ProofTreeUtils.currentDiagonal)
    // .style("opacity", 0)

  }

  export function onLinkExit(s: ProofTreeTypes.LinkSelection): void {
    s.transition()
      .attr("d", d => {
        d.source.parent
        return HierarchyNodeUtils.getHierarchyGoalAncestor(d.source).caseOf<string>({
          nothing: () => ProofTreeUtils.currentDiagonal({ source: d.source, target: d.source }),
          just: g => ProofTreeUtils.currentDiagonal({ source: g, target: g })
        })
      })
      // .style("opacity", "0")
      .remove()
  }

  export function onLinkUpdatePostMerge(s: ProofTreeTypes.LinkSelection): void {
    s.transition()
      // .style("opacity", 1)
      .attr("d", d => {
        return ProofTreeUtils.destinationDiagonal({ "source": d.source, "target": d.target })
      })
      .attr("stroke-width", d => d.source.data.proofTree.linkWidth(d))
  }
