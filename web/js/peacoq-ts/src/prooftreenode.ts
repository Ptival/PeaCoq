import * as ProofTreeUtils from "./prooftree-utils";

export abstract class ProofTreeNode implements IProofTreeNode {
  private body: HTMLElement;
  depth: number;
  id: string;
  label: string;
  proofTree: IProofTree;
  x: number;
  x0: number;
  y: number;
  y0: number;

  constructor(proofTree: IProofTree, parent: Maybe<IProofTreeNode>) {
    this.body = undefined;
    this.depth = parent.caseOf({
      nothing: () => 0,
      just: (parent) => parent.depth + 1,
    });
    this.id = _.uniqueId();
    this.proofTree = proofTree;
  }

  abstract click(): void;

  abstract getAllDescendants(): IProofTreeNode[];
  abstract getAllGoalDescendants(): IGoalNode[];
  abstract getFocusedChild(): Maybe<ProofTreeNode>;
  abstract getGoalAncestor(): Maybe<IGoalNode>;
  abstract getHeight(): number;

  getHTMLElement(): HTMLElement {
    if (!this.body) {
      console.log("BAD: missing this.body", this);
    }
    //assert(this.body !== undefined, "ProofTreeNode.getHTMLElement");
    return this.body;
  }

  getOriginalScaledX(): number {
    return this.getScaledX();
    // let self = this;
    // return this.getGoalAncestor().caseOf({
    //   // the root needs to spawn somewhere arbitrary: (0, 0.5)
    //   nothing: () => self.proofTree.xOffset(self),
    //   // non-roots are spawned at their parent's (cX0, cY0)
    //   // just: (p) => + $(p.body.parentElement).attr("x"),
    //   just: (p) => self.getScaledX(),
    // });
  }

  getOriginalScaledY(): number {
    return this.getScaledY();
    // let self = this;
    // let tree = this.proofTree;
    // return this.getGoalAncestor().caseOf({
    //   // the root needs to spawn somewhere arbitrary: (0, 0.5)
    //   nothing: () => 0.5 * tree.xOffset(self) + tree.yOffset(self),
    //   // non-roots are spawned at their parent's (cX0, cY0)
    //   // just: (p) => + $(p.body.parentElement).attr("y"),
    //   just: (p) => self.getScaledY(),
    // });
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
