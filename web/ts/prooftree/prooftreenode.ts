import { commonAncestor } from "./common-ancestor"

export abstract class ProofTreeNode implements IProofTreeNode {
  private body: HTMLElement | undefined
  public currentScaledX: number
  public currentScaledY: number
  public depth: number
  public id: string
  public label: string
  // public x: number
  // x0: number
  // public y: number
  // y0: number

  constructor(
    public proofTree: IProofTree,
    parent: Maybe<IProofTreeNode>
  ) {
    this.body = undefined
    this.depth = parent.fmap(p => p.depth + 1).valueOr(0)
    const foo = parent.fmap(p => p.currentScaledX).valueOr(0)
    this.currentScaledX = parent.fmap(p => p.currentScaledX).valueOr(0)
    this.currentScaledY = parent.fmap(p => p.currentScaledY).valueOr(0)
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
  //   const tree = this.proofTree
  //   return this.getGoalAncestor().caseOf({
  //     // the root needs to spawn somewhere arbitrary: (0, 0.5)
  //     nothing: () => 0.5 * tree.xOffset(this) + tree.yOffset(this),
  //     // non-roots are spawned at their parent's (cX0, cY0)
  //     // just: (p) => + $(p.body.parentElement).attr("y"),
  //     just: (p) => this.getScaledDestinationY(),
  //   })
  // }

  public abstract getParent(): Maybe<IProofTreeNode>

  // public getDestinationScaledX(): number {
  //   const tree = this.proofTree
  //   debugger
  //   return ProofTreeUtils.nodeX(this) * tree.xFactor + tree.xOffset(this)
  // }

  // public getDestinationScaledY(): number {
  //   const tree = this.proofTree
  //   return ProofTreeUtils.nodeY(this) * tree.yFactor + tree.yOffset(this)
  // }

  public abstract getViewChildren(): IProofTreeNode[]

  public getViewGrandChildren(): IProofTreeNode[] {
    return (
      _(this.getViewChildren())
        .map(e => e.getViewChildren())
        .flatten<ProofTreeNode>(true)
        .value()
    )
  }

  public abstract getWidth(): number

  public hasGrandParent(): boolean {
    return this.hasParentSuchThat(p => p.hasParent())
  }

  public hasParent(): boolean { return this.hasParentSuchThat(() => true) }

  public hasParentSuchThat(pred: (_1: IProofTreeNode) => boolean): boolean {
    return this.getParent().fmap(pred).valueOr(false)
  }

  public isCurNode(): boolean {
    return this.id === this.proofTree.curNode.id
  }

  public isCurNodeAncestor(): boolean {
    const curNode = this.proofTree.curNode
    const common = commonAncestor(curNode, this)
    return this.id === common.id
  }

  public abstract isSolved(): boolean

  public setHTMLElement(e: HTMLElement): void {
    this.body = e
  }

}
