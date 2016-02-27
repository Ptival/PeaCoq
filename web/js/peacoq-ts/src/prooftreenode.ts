
abstract class ProofTreeNode {
  private _cX: number;
  private cX0: number;
  private _cY: number;
  private cY0: number;
  depth: number;
  height: number;
  id: string;
  label: string;
  proofTree: ProofTree;
  response: any; // TODO: remove this
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

  get cX(): number {
    if (this._cX === undefined) {
      throw this;
    }
    return this._cX;
  }
  set cX(x: number) {
    this._cX = x;
  }
  get cY(): number {
    if (this._cY === undefined) {
      throw this;
    }
    return this._cY;
  }
  set cY(y: number) {
    this._cY = y;
  }

  abstract getAllDescendants(): ProofTreeNode[];
  abstract getAllGoalDescendants(): GoalNode[];
  abstract getFocusedChild(): Maybe<ProofTreeNode>;

  get originalScaledX(): number {
    if (this.cX0 === undefined) {
      throw this;
    }
    return this.cX0;
  }

  set originalScaledX(x: number) {
    this.cX0 = x;
  }

  get OriginalScaledY(): number {
    if (this.cY0 === undefined) {
      throw this;
    }
    return this.cY0;
  }

  set originalScaledY(x: number) {
    this.cY0 = x;
  }

  abstract getParent(): Maybe<ProofTreeNode>;
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
