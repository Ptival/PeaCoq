
abstract class ProofTreeNode {
  cX: number;
  cY: number;
  depth: number;
  height: number;
  id: string;
  label: string;
  proofTree: ProofTree;
  width: number;
  x: number;
  x0: number;
  y: number;
  y0: number;

  constructor(proofTree: ProofTree, parent: TsMonad.Maybe<ProofTreeNode>) {
    this.depth = parent.caseOf({
      nothing: () => 0,
      just: (parent) => parent.depth + 1,
    });
    this.id = _.uniqueId();
    this.proofTree = proofTree;
  }

  abstract click(): void;

  abstract getAllDescendants(): ProofTreeNode[];
  abstract getAllGoalDescendants(): GoalNode[];
  abstract getFocusedChild(): Maybe<ProofTreeNode>;

  getOriginalScaledX(): number {
    let self = this;
    return this.getParent().caseOf({
      // the root needs to spawn somewhere arbitrary: (0, 0.5)
      nothing: () => self.proofTree.xOffset(self),
      // non-roots are spawned at their parent's (cX0, cY0)
      just: (p) => p.getOriginalScaledX(),
    });
  }

  getOriginalScaledY(): number {
    let self = this;
    let tree = this.proofTree;
    return this.getParent().caseOf({
      // the root needs to spawn somewhere arbitrary: (0, 0.5)
      nothing: () => 0.5 * tree.xOffset(self) + tree.yOffset(self),
      // non-roots are spawned at their parent's (cX0, cY0)
      just: (p) => p.getOriginalScaledY(),
    });
  }

  abstract getParent(): Maybe<ProofTreeNode>;

  getScaledX(): number {
    let tree = this.proofTree;
    return nodeX(this) * tree.xFactor + tree.xOffset(this);
  }

  getScaledY(): number {
    let tree = this.proofTree;
    return nodeY(this) * tree.yFactor + tree.yOffset(this);
  }

  abstract getViewChildren(): ProofTreeNode[];

  getViewGrandChildren(): ProofTreeNode[] {
    return (
      _(this.getViewChildren())
        .map(function(e) { return e.getViewChildren(); })
        .flatten<ProofTreeNode>(true)
        .value()
    );
  }

  hasGrandParent(): boolean {
    return this.hasParentSuchThat((p) => p.hasParent());
  }

  hasParent(): boolean { return this.hasParentSuchThat(() => true); }

  hasParentSuchThat(pred: (_1: ProofTreeNode) => boolean): boolean {
    return this.getParent().caseOf({
      nothing: () => false,
      just: (p) => pred(p),
    });
  }

  isCurNodeAncestor() {
    let curNode = this.proofTree.curNode;
    let common = this.proofTree.commonAncestor(curNode, this);
    return this.id === common.id;
  }

  abstract isSolved(): boolean;
  abstract nodeWidth(): number;

}
