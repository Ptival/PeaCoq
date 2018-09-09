import * as d3Hierarchy from 'd3-hierarchy'
import * as d3Interpolate from 'd3-interpolate'
import * as d3Path from 'd3-path'
import * as d3Selection from 'd3-selection'
import * as d3Transition from 'd3-transition'
import * as _ from 'lodash'
import { debounceAndThrottle } from '../rxjs/operators'
import { Maybe } from 'tsmonad'

import { commonAncestor } from './common-ancestor'
import { FakeNode } from './fakenode'
import { GoalNode } from './goalnode'
import * as HierarchyNodeUtils from './hierarchy-node-utils'
import * as LinkSelection from './link-selection'
import * as RectSelection from './rect-selection'
import { TacticGroupNode } from './tacticgroupnode'
import * as TextSelection from './text-selection'
import { Strictly } from '../peacoq/strictly'
import * as ProofTreeUtils from './utils'

type HTMLElementSelection = ProofTreeTypes.HTMLElementSelection

d3Transition // forces the import

function byNodeId(d : ProofTreeTypes.Node) : string { return d.data.id }
function byLinkId(d : ProofTreeTypes.Link) : string { return `${d.source.data.id}, ${d.target.data.id}` }

/* Globals to be configured */
const animationDuration = 800
// const diffBlue = '#8888EE'
// const diffGreen = '#88EE88'
// const diffOrange = '#FFB347'
// const diffOpacity = 0.75
// const diffRed = '#EE8888'
const goalBodyPadding = 4
const verticalSpacingBetweenNodes = 10

function pairwise<T>(a : T[]) : [T, T][] {
    const zipped = _.zip(
        a,
        a.slice(1)
    )
    zipped.pop() // removes [last, undefined] at the end
    return _.flatMap<[T | undefined, T | undefined][], [T, T]>(
        zipped,
        ([a, b] : [T | undefined, T | undefined]) : [T, T][] => {
            if (!a || !b) { return [] }
            return [ [a, b] ]
        }
    )
}

export class ProofTree implements IProofTree {
    public descendantsOffset : number
    public readonly curNode$ : Rx.Subject<IGoalNode>
    public rootNode : IGoalNode
    public tacticWaiting : Maybe<string>
    public xFactor : number
    public yFactor : number

    private anchor : ProofTreeTypes.HTMLElementSelection
    private _curNode : IGoalNode
    private paused : boolean
    private svgId : string
    private tactics : () => TacticGroup[]
    private tacticsWorklist : WorklistItem[]
    private hierarchyRoot : d3Hierarchy.HierarchyNode<IProofTreeNode>
    private treeRoot : d3Hierarchy.HierarchyPointNode<IProofTreeNode>
    private updateSubject : Rx.Subject<{}>
    private usingKeyboard : boolean /* true until the user uses their mouse */
    private viewportX : number
    private viewportY : number

    private div : HTMLElementSelection
    private svg : HTMLElementSelection
    private viewport : HTMLElementSelection
    private linkLayer : HTMLElementSelection
    private rectLayer : HTMLElementSelection
    private diffLayer : HTMLElementSelection
    private textLayer : HTMLElementSelection
    private tipsLayer : HTMLElementSelection

    constructor(
        public name : string,
        anchor : HTMLElement,
        private width : number,
        private height : number,
        parent : Maybe<ITacticGroupNode>,
        public context : PeaCoqContext,
        public index : number,
        public document : ICoqDocument
    ) {
        width = Math.max(0, width)
        this.width = width
        height = Math.max(0, height)
        this.height = height

        this.anchor = d3Selection.select(anchor)

        this.paused = false
        this.svgId = _.uniqueId()
        this.xFactor = this.width
        this.yFactor = this.height
        this.usingKeyboard = true // true until the user moves their mouse
        this.tacticWaiting = nothing<string>()

        this.rootNode = new GoalNode(this, parent, context, index)

        this._curNode = this.rootNode
        this.curNode$ = new Rx.BehaviorSubject(this.rootNode)

        // debugger
        this.treeRoot = ProofTreeUtils.makeHierarchyTree(this)

        d3Selection.select('body')
            .on('keydown', () => {
                // capture events only if we are in proof mode
                if ($(' :focus').length === 0) {
                    this.keydownHandler()
                }
            })

        this.div = this.anchor
            .insert('div', ' :first-child')
            .attr('id', 'pt-' + this.svgId)
            .classed('prooftree', true)
            .style('overflow', 'hidden')

        this.svg = this.div
            .insert('svg', ' :first-child')
            .classed('svg', true)
            .attr('id', 'svg-' + this.svgId)
        // necessary for the height to be exactly what we set
            .attr('display', 'block')
            .style('width', this.width + 'px')
            .style('height', this.height + 'px')
        // also need these as attributes for svg_todataurl
            .attr('width', this.width + 'px')
            .attr('height', this.height + 'px')
        // .attr('focusable', true)
        // this creates a blue outline that changes the width weirdly
        // .attr('tabindex', 0)
        // for debugging, this is useful
        // .attr('viewBox', '0 -100 1000 400')

        // debugger
        this.viewport =
            this.svg
            .append('g')
            .attr('id', 'viewport') // for SVGPan.js
            .attr('class', 'viewport')
            .attr(
                'transform',
                'translate(' + this.getGoalWidth() + ', 0)'
            )

        // note : the order of these influence the display
        // from bottom layers
        this.linkLayer = this.viewport.append('g').attr('id', 'link-layer')
        this.rectLayer = this.viewport.append('g').attr('id', 'rect-layer')
        this.diffLayer = this.viewport.append('g').attr('id', 'diff-layer')
        this.textLayer = this.viewport.append('g').attr('id', 'text-layer')
        this.tipsLayer = this.viewport.append('g').attr('id', 'tips-layer')
        // to top layers

        // if (svgPanEnabled) {
        //   this.svg.insert('script', ' :first-child').attr('xlink :href', 'SVGPan.js')
        // }

        this.updateSubject = new Rx.Subject()

        // Why?
        Rx.Observable.interval(2000).subscribe(() => this.updateSubject.onNext({}))

        // TODO : figure out why I was doing this and whether I can avoid it
        // this updates the display every second
        this.updateSubject
            .let(debounceAndThrottle(1000))
            .subscribe(() => this.updateAndWait())

    }

    public cleanup() {
        this.curNode$.onCompleted()
    }

    public getAllGoals() : IGoalNode[] {
        return ([] as IGoalNode[]).concat(
            [this.rootNode],
            this.rootNode.getAllGoalDescendants()
        )
    }

    get curNode() : IGoalNode { return this._curNode }
    set curNode(n : IGoalNode) {
        if (n.id !== this._curNode.id) {
            // debugger
            // console.log('Switching current node to', n)
            this._curNode = n
            n.focus()
            this.curNode$.onNext(n)
        }
    }

    public getGoalWidth() {
        const goalShare = 15 / 20
        return Math.floor(this.width * (goalShare / 2))
    }

    public getHierarchyCurNode() : ProofTreeTypes.Node {
        const found = this.treeRoot.descendants().find(d => d.data.id === this.curNode.id)
        if (found === undefined) {
            debugger
            throw tantrum
        }
        return found
    }

    public getTacticWidth() {
        const tacticShare = 4 / 20
        return Math.floor(this.width * (tacticShare / 2))
    }

    public isCurNode(n : IProofTreeNode) : boolean { return n.id === this.curNode.id }

    public isCurNodeAncestor(strictly : Strictly, n : IProofTreeNode) : boolean {
        const common = commonAncestor(n, this.curNode)
        const commonAncestorIsNode = common.id === n.id
        switch (strictly) {
            case Strictly.Yes : return commonAncestorIsNode && !this.isCurNode(n)
            case Strictly.No : return commonAncestorIsNode
        }
        throw 'ProofTree.isCurNodeAncestor'
    }

    public requestNext() : void {
        this.document.next()
    }

    public resize(width : number, height : number) {
        this.width = Math.floor(width)
        this.height = Math.floor(height)
        this.svg
            .style('width', `${this.width}px`)
            .style('height', `${this.height}px`)
        // also need these as attributes for svg_todataurl
            .attr('width', `${this.width}px`)
            .attr('height', `${this.height}px`)

        this.scheduleUpdate()
    }

    public scheduleUpdate() : void {
        this.updateSubject.onNext({})
    }

    public updateAndWait() : Promise<{}> {
        // console.trace(new Date())
        return new Promise((onFulfilled, onRejected) => {
            this.updatePromise(
                () => {
                    // console.log('UPDATE : DONE')
                    onFulfilled()
                },
                onRejected
            )
        })
    }

    // public xOffset(d : ProofTreeTypes.Node) : number {
    //   return - d.data.getWidth() / 2 // position the center
    // }

    // public yOffset(d : ProofTreeTypes.Node) : number {
    //   const offset = - d.data.getHeight() / 2 // for the center
    //   const focusedChild = this.curNode.getFocusedChild()

    //   // all tactic nodes are shifted such that the current tactic is centered
    //   // assert(isGoal(this.curNode), 'yOffset assumes the current node is a goal!')
    //   if (this.isCurGoalChild(d.data)) {
    //     // assert(focusedChild !== undefined, 'yOffset : focusedChild === undefined')
    //     return offset + (
    //       ProofTreeUtils.nodeY(d.parent) - ProofTreeUtils.nodeY(fromJust(focusedChild))
    //     ) * this.yFactor
    //   }

    //   // all goal grandchildren are shifted such that the context line of the
    //   // current goal and the current suboal align
    //   if (this.isCurGoalGrandChild(d.data)) {
    //     return offset + this.descendantsOffset
    //   }

    //   // we center the curNode parent to its focused child
    //   if (this.isCurNodeParent(d.data)) {
    //     if (d instanceof TacticGroupNode) {
    //       return offset + (
    //         ProofTreeUtils.nodeY(this.curNode) - ProofTreeUtils.nodeY(d)
    //       ) * this.yFactor
    //     } else {
    //       // This should not happen anymore (should not be a GoalNode)
    //       debugger
    //     }
    //   }

    //   // the other nodes (current goal and its ancestors) stay where they need
    //   return offset
    // }

    private findNodeInTree<T extends IProofTreeNode>(n : T) : d3Hierarchy.HierarchyPointNode<T> {
        if (n.id === undefined) { debugger } // this happened before...
        const found = this.treeRoot.descendants().find(d => d.data.id === n.id)
        if (found === undefined) {
            debugger
            throw 'findNodeInTree'
        }
        return found as any
    }

    /*
      here we are looking for the descendant which should align with the current
      node. it used to be at the top of the view, now it's centered.
    */
    private computeDescendantsOffset() {
        const curNode = this.findNodeInTree(this.curNode)

        const centeredDescendant : Maybe<IProofTreeNode> =
            this.curNode.getViewFocusedChild().caseOf<Maybe<IProofTreeNode>>({
                nothing : () => nothing<IProofTreeNode>(),
                just : fc => fc.getFocusedChild().caseOf<Maybe<IProofTreeNode>>({
                    nothing : () => just(fc),
                    just : (fgc : IProofTreeNode) => just(fgc),
                })
            })

        centeredDescendant.caseOf({
            nothing : () => { this.descendantsOffset = 0 },
            just : d => {
                const treeD = this.findNodeInTree(d)
                if (d instanceof GoalNode) {
                    // computing the difference in height between the <hr> is not
                    // obvious...
                    const hrDelta = curNode.data.html[0].offsetTop - d.html[0].offsetTop
                    this.descendantsOffset = (
                        this.yFactor * (ProofTreeUtils.nodeY(curNode) - ProofTreeUtils.nodeY(treeD))
                            - (curNode.data.getHeight() - d.getHeight()) / 2
                            + hrDelta
                    )
                } else {
                    this.descendantsOffset =
                        this.yFactor * (ProofTreeUtils.nodeY(curNode) - ProofTreeUtils.nodeY(treeD))

                }
            }
        })

    }

    private computeXYFactors() {
        const curGoal = this.getHierarchyCurNode()
        // huh cf. https ://github.com/DefinitelyTyped/DefinitelyTyped/issues/11365
        const visibleChildren = curGoal.children || []
        const visibleGrandChildren = visibleChildren.reduce<ProofTreeTypes.Node[]>(
            (acc, elt) => acc.concat(elt.children || []), []
        )
        const visibleNodes = ([] as ProofTreeTypes.Node[]).concat(
            (curGoal.parent !== null) ? [curGoal.parent] : [],
            [curGoal],
            visibleChildren,
            visibleGrandChildren
        )

        // xFactor is now fixed, so that the user experience is more stable
        const rootViewChildren = this.rootNode.getViewChildren()
        if (rootViewChildren.length === 0) {
            this.xFactor = this.width
        } else {
            const treeFirstChildren = this.findNodeInTree(rootViewChildren[0])
            const treeRootNode = this.findNodeInTree(this.rootNode)
            const xDistance = ProofTreeUtils.nodeX(treeFirstChildren) - ProofTreeUtils.nodeX(treeRootNode)
            if (xDistance === 0) {
                debugger
            }
            /* width = 4 * xDistance * xFactor */
            this.xFactor = this.width / (4 * xDistance)
        }

        /*
          we want all visible grand children to be apart from each other
          i.e.
          ∀ a b, yFactor * | a.y - b.y | > a.height/2 + b.height/2 + nodeVSpacing
          we also want all visible children to be apart from each other (especially
          when they don't have their own children to separate them)
        */
        const gcSiblings = pairwise(visibleGrandChildren)
        const cSiblings = pairwise(visibleChildren)
        // also, the current node should not overlap its siblings
        let currentSiblings : [ProofTreeTypes.Node, ProofTreeTypes.Node][] = []
        const curParent = curGoal.parent
        if (this.curNode instanceof GoalNode && curParent !== null) {
            const curNodeSiblings = curParent.children || []
            currentSiblings = pairwise(curNodeSiblings)
        }
        const siblings = _(gcSiblings.concat(cSiblings, currentSiblings))
        // debugger
        const yFactors = siblings
            .map(e => {
                const a = e[0], b = e[1]
                const yDistance = ProofTreeUtils.nodeY(b) - ProofTreeUtils.nodeY(a)
                if (yDistance === 0) {
                    debugger
                    return 1
                }
                const wantedSpacing = ((a.data.getHeight() + b.data.getHeight()) / 2) + verticalSpacingBetweenNodes
                return wantedSpacing / yDistance
            })
            .value()

        const newYFactor = _.isEmpty(yFactors) ? this.height : _.max(yFactors)
        if (newYFactor !== undefined) {
            this.yFactor = newYFactor
        }
        else {
            console.log('Not updating yFactor, check this out...')
        }

        // This has happened many times!!!
        if (!Number.isFinite(this.xFactor)) { debugger }
        if (!Number.isFinite(this.yFactor)) { debugger }
    }

    private getAllNodes() : IProofTreeNode[] { return this.rootNode.getAllDescendants() }

    private getCurrentGoal() : IGoalNode {
        assert(this.curNode instanceof GoalNode, 'getCurrentGoal : curNode instanceof GoalNode')
        return this.curNode
    }

    private getFocus() { $(' :focus').blur() }

    private getCurrentScale() {
        return (<any>this.svg[0][0]).currentScale
    }

    /*
      getFocusedGoal() : GoalNode {
      const focusedChild = this.curNode.getFocusedChild()
      if (focusedChild !== undefined) {
      //if (focusedChild instanceof GoalNode) { return focusedChild }
      const focusedGrandChild = focusedChild.getFocusedChild()
      if (focusedGrandChild !== undefined) {
      return focusedGrandChild
      }
      }
      return undefined
      }
    */

    private isCurGoal(n : IProofTreeNode) : boolean {
        return n.id === this.curNode.id
    }

    private isCurGoalChild(n : IProofTreeNode) : boolean {
        return n.hasParentSuchThat(p => this.isCurGoal(p))
    }

    private isCurGoalGrandChild(n : IProofTreeNode) : boolean {
        return n.hasParentSuchThat(p => this.isCurGoalChild(p))
    }

    private isCurNodeChild(n : IProofTreeNode) : boolean {
        return n.hasParentSuchThat(p => this.isCurNode(p))
    }

    private isCurNodeDescendant(strictly : Strictly, n : IProofTreeNode) : boolean {
        const common = commonAncestor(n, this.curNode)
        const commonAncestorIsCurNode = common.id === this.curNode.id
        switch (strictly) {
            case Strictly.Yes : return commonAncestorIsCurNode && !this.isCurNode(n)
            case Strictly.No : return commonAncestorIsCurNode
        }
        throw 'ProofTree.isCurNodeDescendant'
    }

    private isCurNodeGrandChild(n : IProofTreeNode) : boolean {
        return n.hasParentSuchThat(p => this.isCurNodeChild(p))
    }

    private isCurNodeParent(n : IProofTreeNode) : boolean {
        return this.curNode.hasParentSuchThat(p => p.id === n.id)
    }

    // isCurNodeSibling(n : ProofTreeNode) : boolean {
    //   return !this.isCurNode(n) && hasParent(n) && this.isCurNodeParent(n.getParent())
    // }

    private isRootNode(n : IProofTreeNode) : boolean {
        return n.id === this.rootNode.id
    }

    private keydownHandler() {
        debugger // how does this work in D3 4.0?
        // const ev : any = d3.event
        // // don't interact while typing
        // if (ev.target.type === 'textarea') { return }
        // const curNode = this.curNode
        // const children = curNode.getViewChildren()
        // this.usingKeyboard = true
        // // console.log(d3.event.keyCode)

        // switch (ev.keyCode) {

        //   case 37 : // Left
        //     // case 65 : // a
        //     ev.preventDefault()
        //     curNode.getParent().caseOf({
        //       nothing : () => {
        //         // when at the root node, undo the last action (usually Proof.)
        //         // onCtrlUp(false)
        //       },
        //       just : parent => {
        //         // asyncLog('LEFT ' + nodeString(curNode.parent))
        //         parent.click()
        //       },
        //     })
        //     break

        //   case 39 : // Right
        //     // case 68 : // d
        //     ev.preventDefault()
        //     curNode.getFocusedChild().fmap(dest => {
        //       // asyncLog('RIGHT ' + nodeString(dest))
        //       dest.click()
        //     })
        //     break

        //   //   case 38 : // Up
        //   //     //case 87 : // w
        //   //     ev.preventDefault()
        //   //     if (ev.shiftKey) {
        //   //       //this.shiftPrevGoal(curNode.getFocusedChild())
        //   //     } else {
        //   //       this.shiftPrevByTacticGroup(curNode)
        //   //     }
        //   //     break
        //   //
        //   //   case 40 : // Down
        //   //     //case 83 : // s
        //   //     ev.preventDefault()
        //   //     if (ev.shiftKey) {
        //   //       //this.shiftNextGoal(curNode.getFocusedChild())
        //   //     } else {
        //   //       this.shiftNextByTacticGroup(curNode)
        //   //     }
        //   //     break
        //   //
        //   //   case 219 : // [
        //   //     var focusedChild = curNode.getFocusedChild()
        //   //     focusedChild.fmap((c) => (<TacticGroupNode>c).shiftPrevInGroup())
        //   //     break
        //   //
        //   //   case 221 : // ]
        //   //     var focusedChild = curNode.getFocusedChild()
        //   //     focusedChild.fmap((c) => (<TacticGroupNode>c).shiftNextInGroup())
        //   //     break

        //   default :
        //     console.log('Unhandled event', (d3.event as any).keyCode)
        //     return
        // }

        // // EDIT : now that we integrate the proof tree, it's best to const stuff bubble up
        // // if we haven't returned, we don't want the normal key behavior
        // // d3.event.preventDefault()

    }

    public linkWidth(d : ProofTreeTypes.Link) : string {
        const src = d.source
        const tgt = d.target
        const thin = '2px'
        const thick = '5px'
        // if the user uses his mouse, highlight the path under hover
        /*
          if (!this.usingKeyboard) {
          if (this.hoveredNode === undefined) {
          return thin
          } else {
          if (this.isCurNode(src)) {
          if (sameNode(tgt, this.hoveredNode)) { return thick }
          else if (!hasParent(this.hoveredNode)) { return thin }
          else if (sameNode(tgt, this.hoveredNode.parent)) {
          return thick
          }
          else { return thin }
          } else if (this.isCurNodeChild(src)) {
          if (sameNode(tgt, this.hoveredNode)) { return thick }
          else { return thin }
          } else {
          return thin
          }
          }
          }
        */

        const curNode = this.curNode

        // if the user uses his keyboard, highlight the focused path
        // if (curNode instanceof GoalNode) {

        return this.curNode.getFocusedChild().caseOf({
            nothing : () => thin,
            just : (focusedChild) => {
                if (this.isCurNode(src.data) && focusedChild.id === tgt.id) { return thick }
                return focusedChild.getFocusedChild().caseOf({
                    nothing : () => thin,
                    just : (focusedGrandChild) => {
                        return (
                            focusedChild.id === src.id && focusedGrandChild.id === tgt.id
                                ? thick : thin
                        )
                    },
                })
            },
        })

        //
        // } else if (curNode instanceof TacticGroupNode) {
        //   const focusedChild = this.curNode.getFocusedChild()
        //   if (focusedChild !== undefined && tgt.id === focusedChild.id) {
        //     return thick
        //   }
        //   return thin
        // } else {
        //   throw this.curNode
        // }

    }

    private processTactics() : Promise<any> {

        /*
          every time curNode is changed, the tacticsWorklist should be
          flushed, so that [runTactic] can reliably add the results of running
          the tactic to the current node
        */

        const promiseSpark = this.tacticsWorklist.shift()

        if (promiseSpark === undefined) {
            return Promise.resolve()
        }

        return promiseSpark()
        // delay for testing purposes
        // .then(delayPromise(0))
            .then(this.processTactics.bind(this))
            .catch(outputError)

                }

    private refreshTactics() : void {
        // if (focusedOnEditor) { return }

        const self = this
        const curNode = this.curNode

        const tacticsAndGroups = this.tactics()

        /*
          _(this.tactics())
          .groupBy(function(elt) {
          if ($.type(elt) === 'string') {
          return 'tactics'
          } else {
          return 'groups'
          }
          })
          .value()

          // TODO : there should be no tactics!
          const groups = tacticsAndGroups.groups
        */

        /*
          const groupSparks = _(tacticsAndGroups)
          .map(function(group) {
          const groupNode : TacticGroupNode = self.findOrCreateGroup(curNode, group.name)
          return (
          _(group.tactics)
          .filter(
          tactic => {
          return (
          !_(groupNode.tactics)
          .some(function(node) {
          return (node.tactic === tactic)
          })
          )
          })
          .map(
          tactic => {
          return function() {
          return self.runTactic(tactic, groupNode)
          }
          })
          .flatten(true)
          .value()
          )
          })
          .flatten<() => Promise<any>>(true)
          .value()

          // flushes the worklist and add the new sparks
          this.tacticsWorklist = groupSparks
        */
        // console.log('REPOPULATING TACTICS WORKLIST', this.tacticsWorklist)

        this.processTactics()
    }

    private resetSVGTransform() : void {
        const transform = this.viewport.attr('transform')
        if (transform.length === 0) { return }
        let m = parseSVGTransform(transform)
        if (m.hasOwnProperty('matrix')) {
            m = m.matrix
            this.viewport.attr(
                'transform',
                `matrix(1, ${m[1]}, ${m[2]}, 1, ${m[4]}, ${m[5]})`
            )
        }
    }

    // private runTactic(t : string, groupToAttachTo) {
    //   /*
    //       const self = this

    //       const parentGoal = getClosestGoal(groupToAttachTo)
    //       const parentGoalRepr = goalNodeUnicityRepr(parentGoal)

    //       // if we correctly stored the last response in [parentGoal], we don't need
    //       // to query for status at this moment
    //       const beforeResponse = parentGoal.response

    //       $('#loading-text').text(nbsp + nbsp + 'Trying ' + t)

    //       return asyncQueryAndUndo(t)
    //         //.then(delayPromise(0))
    //         .then(function(response) {
    //           if (isGood(response)) {

    //             //const unfocusedBefore = getResponseUnfocused(beforeResponse)
    //             //const unfocusedAfter = getResponseUnfocused(response)
    //             const newChild = new Tactic(
    //               t,
    //               groupToAttachTo,
    //               response
    //             )

    //             // only attach the newChild if it produces something
    //             // unique from existing children
    //             const newChildRepr = tacticUnicityRepr(newChild)

    //             const resultAlreadyExists =
    //               _(parentGoal.getTactics()).some(function(t) {
    //                 return t.tactic === newChild.tactic
    //                 //return (tacticUnicityRepr(t) === newChildRepr)
    //               })

    //             const tacticIsUseless =
    //               (newChild.goals.length === 1)
    //               && (goalNodeUnicityRepr(newChild.goals[0])
    //                 === parentGoalRepr)

    //             if (!resultAlreadyExists && !tacticIsUseless) {
    //               groupToAttachTo.addTactic(newChild)
    //               self.update()
    //             }

    //           } else {

    //             //console.log('Bad response for', t, response)

    //           }

    //         })
    //         .catch(outputError)
    //   */
    // }

    private shiftNextByTacticGroup(n : IGoalNode) : void {
        if (this.paused) { return }
        if (n.isSolved()) { return }
        const viewChildren = n.getViewChildren()
        if (n.tacticIndex + 1 < viewChildren.length) {
            n.tacticIndex++
            // asyncLog('DOWNGROUP ' + nodeString(viewChildren[n.tacticIndex]))
            this.scheduleUpdate()
        }
    }

    private shiftPrevByTacticGroup(n : IGoalNode) : void {
        if (this.paused) { return }
        if (n.isSolved()) { return }
        if (n.tacticIndex > 0) {
            n.tacticIndex--
            // asyncLog('UPGROUP ' + nodeString(n.getViewChildren()[n.tacticIndex]))
            this.scheduleUpdate()
        }
    }

    private updatePromise<T>(onFulfilled : () => void, onRejected : () => void) : void {
        console.trace('updatePromise')
        const curNode = this.curNode

        this.resetSVGTransform() // cancel view transformations

        this.treeRoot = ProofTreeUtils.makeHierarchyTree(this)
        const allNodes = this.treeRoot.descendants()
        const allLinks = this.treeRoot.links()

        // now remove all fake nodes
        const nodes = allNodes
            .filter(node => !(node instanceof FakeNode))

        const links = allLinks
            .filter(link => !(link.source instanceof FakeNode || link.target instanceof FakeNode))

        const nodeArray = nodes.entries

        // we build the foreignObject first, as its dimensions will guide the others
        const textSelection = this.textLayer
            .selectAll<Element, ProofTreeTypes.Node>((d, i, nodes) => {
                return (nodes[i] as Element).getElementsByTagName('foreignObject')
            })
            .data(nodes, d => d.data.id)

        // Here we need select({}) because d3 transitions are exclusive and
        // without it, concurrent selections will not each call their 'end'
        // callback.
        // See. https ://bl.ocks.org/mbostock/5348789
        d3Selection.select({} as any)
            .transition()
            .duration(animationDuration)
            .each(() => {

                const textEnter = textSelection.enter().append('foreignObject')
                const rectSelection = this.rectLayer.selectAll('rect').data<ProofTreeTypes.Node>(nodes, byNodeId)
                const linkSelection = this.linkLayer.selectAll('path').data<ProofTreeTypes.Link>(links, byLinkId)

                /*
                  Here, we must rely on the DOM to compute the height of nodes, so
                  that we can position them accordingly. However, the height is
                  dictated by how the HTML will render for the given width of the
                  nodes. Therefore, we must initially include the HTML within the
                  yet-to-be-placed nodes, and we must set their width so that the
                  renderer computes their height.

                  Once nodes have a height, we can query it, compute the zooming
                  and translating factors, offset the descendant nodes to center
                  the focused one, and start positioning nodes.
                */

                textEnter
                    .append('xhtml :body')
                    .each((d, i, nodes) => {
                        const self = nodes[i]
                        // debugger
                        const body = d3Selection.select(self as Element).node()
                        if (body === null) {
                            debugger
                            return thisShouldNotHappen()
                        }
                        d.data.setHTMLElement(<HTMLElement><any>body)
                        const node = d.data
                        // debugger
                        if (node instanceof GoalNode) { $(body).append(node.html) }
                        if (node instanceof TacticGroupNode) { node.updateNode() }
                        // $(body).prepend(d.id)
                    })
                textEnter.attr('width', d => d.data.getWidth())

                // nodes now have a size, we can compute zooming factors
                this.computeXYFactors()
                // compute how much descendants must be moved to center current
                this.computeDescendantsOffset()

                // console.log('FIXME!!!')

                TextSelection.onTextEnter(textEnter)
                RectSelection.onRectEnter(rectSelection.enter())
                LinkSelection.onLinkEnter(linkSelection.enter())

                RectSelection.onRectUpdatePostMerge(rectSelection)
                TextSelection.onTextUpdatePostMerge(textSelection)

                LinkSelection.onLinkUpdatePostMerge(linkSelection)

                TextSelection.onTextExit(textSelection.exit<ProofTreeTypes.Node>())
                RectSelection.onRectExit(rectSelection.exit<ProofTreeTypes.Node>())
                LinkSelection.onLinkExit(linkSelection.exit<ProofTreeTypes.Link>())

                const hierarchyCurNode = nodes.find(n => n.data.id === curNode.id)
                if (hierarchyCurNode === undefined) {
                    return thisShouldNotHappen()
                }
                const hierarchyCurNodeParent = hierarchyCurNode.parent

                this.viewportX = - (
                    (hierarchyCurNodeParent === null)
                        ? HierarchyNodeUtils.getDestinationScaledX(hierarchyCurNode)
                        : HierarchyNodeUtils.getDestinationScaledX(hierarchyCurNodeParent)
                )

                this.viewportY = - (
                    HierarchyNodeUtils.getDestinationScaledY(hierarchyCurNode)
                        + curNode.getHeight() / 2
                        - this.height / 2
                )

                this.viewport
                    .transition()
                    .attr(
                        'transform',
                        'translate(' + this.viewportX + ', ' + this.viewportY + ')'
                    )

            })
            .on('end', onFulfilled)

    }

}
