import * as ProofTreeUtils from "./utils";

export abstract class ProofTreeNode implements IProofTreeNode {
  private body: HTMLElement | undefined;
  depth: number;
  id: string;
  label: string;
  x: number;
  x0: number;
  y: number;
  y0: number;

  constructor(
    public proofTree: IProofTree,
    parent: Maybe<IProofTreeNode>
  ) {
    this.body = undefined;
    this.depth = parent.caseOf({
      nothing: () => 0,
      just: (parent) => parent.depth + 1,
    });
    this.id = _.uniqueId();
  }

  abstract click(): void;
  abstract focus(): void;

  abstract getAllDescendants(): IProofTreeNode[];
  abstract getAllGoalDescendants(): IGoalNode[];
  abstract getFocusedChild(): Maybe<IProofTreeNode>;
  abstract getGoalAncestor(): Maybe<IGoalNode>;
  abstract getHeight(): number;

  getHTMLElement(): HTMLElement {
    if (this.body === undefined) { debugger; throw this; }
    //assert(this.body !== undefined, "ProofTreeNode.getHTMLElement");
    return this.body;
  }

  getOriginalScaledX(): number {
    // return this.getScaledX();
    return this.getGoalAncestor().caseOf({
      // the root needs to spawn somewhere arbitrary: (0, 0.5)
      nothing: () => this.proofTree.xOffset(this),
      // non-roots are spawned at their parent's (cX0, cY0)
      // just: (p) => + $(p.body.parentElement).attr("x"),
      just: p => this.getScaledX(),
    });
  }

  getOriginalScaledY(): number {
    // return this.getScaledY();
    let tree = this.proofTree;
    return this.getGoalAncestor().caseOf({
      // the root needs to spawn somewhere arbitrary: (0, 0.5)
      nothing: () => 0.5 * tree.xOffset(this) + tree.yOffset(this),
      // non-roots are spawned at their parent's (cX0, cY0)
      // just: (p) => + $(p.body.parentElement).attr("y"),
      just: (p) => this.getScaledY(),
    });
  }

  abstract getParent(): Maybe<IProofTreeNode>;

  getScaledX(): number {
    let tree = this.proofTree;
    return ProofTreeUtils.nodeX(this) * tree.xFactor + tree.xOffset(this);
  }

  getScaledY(): number {
    let tree = this.proofTree;
    return ProofTreeUtils.nodeY(this) * tree.yFactor + tree.yOffset(this);
  }

  abstract getViewChildren(): IProofTreeNode[];

  getViewGrandChildren(): IProofTreeNode[] {
    return (
      _(this.getViewChildren())
        .map(function(e) { return e.getViewChildren(); })
        .flatten<ProofTreeNode>(true)
        .value()
    );
  }

  abstract getWidth(): number;

  hasGrandParent(): boolean {
    return this.hasParentSuchThat((p) => p.hasParent());
  }

  hasParent(): boolean { return this.hasParentSuchThat(() => true); }

  hasParentSuchThat(pred: (_1: IProofTreeNode) => boolean): boolean {
    return this.getParent().caseOf({
      nothing: () => false,
      just: (p) => pred(p),
    });
  }

  isCurNodeAncestor() {
    let curNode = this.proofTree.curNode;
    let common = ProofTreeUtils.commonAncestor(curNode, this);
    return this.id === common.id;
  }

  abstract isSolved(): boolean;

  setHTMLElement(e: HTMLElement): void {
    this.body = e;
  }

}
