import * as d3Interpolate from 'd3-interpolate'
import * as d3Selection from 'd3-selection'
import * as HierarchyNodeUtils from './hierarchy-node-utils'
import { TacticGroupNode } from './tacticgroupnode'

export function onTextEnter(s : ProofTreeTypes.NodeSelection) : void {
    s
        .each(d => console.log('enter', d))
        .attr('x', d => d.data.currentScaledX)
        .attr('y', d => d.data.currentScaledY)
        .attr('width', d => d.data.getWidth())
        .attr('height', d => d.data.getHeight())
        .each(d => console.log('entered', d.x, d.y))
    // .style('opacity', 0)
}

export function onTextExit(s : ProofTreeTypes.NodeSelection) : void {
    s
        .transition()
        .attrTween('x', (d : ProofTreeTypes.Node) : (t : number) => string => {
            const destinationScaledX = HierarchyNodeUtils.getHierarchyGoalAncestor(d).caseOf({
                nothing : () => HierarchyNodeUtils.getDestinationScaledX(d),
                just : (gp : ProofTreeTypes.Node) => HierarchyNodeUtils.getDestinationScaledX(gp),
            })
            const interpolator = d3Interpolate.interpolateRound(d.data.currentScaledX, destinationScaledX)
            return (t : number) => {
                d.data.currentScaledX = interpolator(t)
                return `${d.data.currentScaledX}`
            }
        })
        .attrTween('y', (d : ProofTreeTypes.Node) : (t : number) => string => {
            const destinationScaledY = HierarchyNodeUtils.getHierarchyGoalAncestor(d).caseOf({
                nothing : () => HierarchyNodeUtils.getDestinationScaledY(d),
                just : (gp : ProofTreeTypes.Node) => HierarchyNodeUtils.getDestinationScaledY(gp),
            })
            const interpolator = d3Interpolate.interpolateRound(d.data.currentScaledY, destinationScaledY)
            return (t : number) => {
                d.data.currentScaledY = interpolator(t)
                return `${d.data.currentScaledX}`
            }
        })
    // .style('opacity', '0')
        .remove()
}

export function onTextUpdatePostMerge(s : ProofTreeTypes.NodeSelection) : void {
    s
        .each(d => { if (d.data instanceof TacticGroupNode) { d.data.updateNode() } })
        .transition()
    // .style('opacity', '1')
    // NOTE: we use attrTween to be able to update currentScaledX and currentScaledY
        .attrTween('x', (d, i, a) => {
            const interpolator = d3Interpolate.interpolateRound(d.data.currentScaledX, HierarchyNodeUtils.getDestinationScaledX(d))
            return t => {
                d.data.currentScaledX = interpolator(t)
                return `${d.data.currentScaledX}`
            }
        })
        .attrTween('y', (d, i, a) => {
            const interpolator = d3Interpolate.interpolateRound(d.data.currentScaledY, HierarchyNodeUtils.getDestinationScaledY(d))
            return t => {
                d.data.currentScaledY = interpolator(t)
                return `${d.data.currentScaledY}`
            }
        })
    // the width must be updated (when resizing window horizontally)
        .attr('width', d => d.data.getWidth())
        .attr('height', d => d.data.getHeight())
    // .style('opacity', 1)
        .on('end', (d, i, nodes) => {
            // this is in 'end' so that it does not trigger before nodes are positioned
            d3Selection.select<d3Selection.BaseType, IProofTreeNode>(nodes[i])
                .on('click', dd => {
                    // asyncLog('CLICK ' + nodeString(dd))
                    dd.click()
                })
        })
}
