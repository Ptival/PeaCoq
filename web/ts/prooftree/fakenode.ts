import { ProofTreeNode } from "./prooftreenode";

function fake(f: FakeNode): any {
  debugger; throw f;
}

export class FakeNode extends ProofTreeNode implements IFakeNode {
  constructor(p: IProofTree, parent: IProofTreeNode) {
    super(p, just(parent));
  }

  click(): void { return fake(this); }
  focus(): void { return fake(this); }
  getAllDescendants(): IProofTreeNode[] { return fake(this); }
  getAllGoalDescendants(): IGoalNode[] { return fake(this); }
  getFocusedChild(): Maybe<IProofTreeNode> { return fake(this); }
  getGoalAncestor(): Maybe<IGoalNode> { return fake(this); }
  getHeight(): number { return fake(this); }
  getParent(): Maybe<IProofTreeNode> { return fake(this); }
  getViewChildren(): IProofTreeNode[] { return fake(this); }
  getWidth(): number { return fake(this); }
  isSolved(): boolean { return fake(this); }
}
