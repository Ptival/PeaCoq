import * as ProofTreeUtils from "./utils"

export abstract class ProofTreeNode implements IProofTreeNode {
  private body: HTMLElement | undefined
  public currentScaledX: number
  public currentScaledY: number
  public depth: number
  public id: string
  public label: string
  public x: number
  // x0: number
  public y: number
  // y0: number

  constructor(
    public proofTree: IProofTree,
    parent: Maybe<IProofTreeNode>
  ) {
    this.body = undefined
    this.depth = parent.caseOf({
      nothing: () => 0,
      just: (parent) => parent.depth + 1,
    })
    this.id = _.uniqueId()
    this.currentScaledX = parent.caseOf({
      nothing: () => 0,
      just: (parent) => parent.currentScaledX,
    })
    this.currentScaledY = parent.caseOf({
      nothing: () => 0,
      just: (parent) => parent.currentScaledY,
    })
  }

  public abstract click(): void
  public abstract focus(): void

  public abstract getAllDescendants(): IProofTreeNode[]
  public abstract getAllGoalDescendants(): IGoalNode[]
  public abstract getFocusedChild(): Maybe<IProofTreeNode>
  public abstract getGoalAncestor(): Maybe<IGoalNode>
  public abstract getHeight(): number

  public getHTMLElement(): HTMLElement {
    if (this.body === undefined) {
      debugger
      throw this
    }
    // assert(this.body !== undefined, "ProofTreeNode.getHTMLElement")
    return this.body
  }

  // getOriginalScaledX(): number {
  //   // return this.getScaledX()
  //   return this.getGoalAncestor().caseOf({
  //     // the root needs to spawn somewhere arbitrary: (0, 0.5)
  //     nothing: () => this.proofTree.xOffset(this),
  //     // non-roots are spawned at their parent's (cX0, cY0)
  //     // just: (p) => + $(p.body.parentElement).attr("x"),
  //     just: p => this.getScaledDestinationX(),
  //   })
  // }
  //
  // getOriginalScaledY(): number {
  //   // return this.getScaledY()
  //   let tree = this.proofTree
  //   return this.getGoalAncestor().caseOf({
  //     // the root needs to spawn somewhere arbitrary: (0, 0.5)
  //     nothing: () => 0.5 * tree.xOffset(this) + tree.yOffset(this),
  //     // non-roots are spawned at their parent's (cX0, cY0)
  //     // just: (p) => + $(p.body.parentElement).attr("y"),
  //     just: (p) => this.getScaledDestinationY(),
  //   })
  // }

  public abstract getParent(): Maybe<IProofTreeNode>

  public getDestinationScaledX(): number {
    let tree = this.proofTree
    return ProofTreeUtils.nodeX(this) * tree.xFactor + tree.xOffset(this)
  }

  public getDestinationScaledY(): number {
    let tree = this.proofTree
    return ProofTreeUtils.nodeY(this) * tree.yFactor + tree.yOffset(this)
  }

  public abstract getViewChildren(): IProofTreeNode[]

  public getViewGrandChildren(): IProofTreeNode[] {
    return (
      _(this.getViewChildren())
        .map(function (e) { return e.getViewChildren() })
        .flatten<ProofTreeNode>(true)
        .value()
    )
  }

  public abstract getWidth(): number

  public hasGrandParent(): boolean {
    return this.hasParentSuchThat((p) => p.hasParent())
  }

  public hasParent(): boolean { return this.hasParentSuchThat(() => true) }

  public hasParentSuchThat(pred: (_1: IProofTreeNode) => boolean): boolean {
    return this.getParent().caseOf({
      nothing: () => false,
      just: (p) => pred(p),
    })
  }

  public isCurNodeAncestor() {
    let curNode = this.proofTree.curNode
    let common = ProofTreeUtils.commonAncestor(curNode, this)
    return this.id === common.id
  }

  public abstract isSolved(): boolean

  public setHTMLElement(e: HTMLElement): void {
    this.body = e
  }

}
