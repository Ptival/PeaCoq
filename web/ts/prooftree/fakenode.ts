import { ProofTreeNode } from "./prooftreenode";

export class FakeNode extends ProofTreeNode implements IFakeNode {
  constructor(p: IProofTree, parent: IProofTreeNode) {
    super(p, just(parent));
  }

  click(): void { throw "FakeNode"; }
  getAllDescendants(): IProofTreeNode[] { throw "FakeNode"; }
  getAllGoalDescendants(): IGoalNode[] { throw "FakeNode"; }
  getFocusedChild(): Maybe<IProofTreeNode> { throw "FakeNode"; }
  getGoalAncestor(): Maybe<IGoalNode> { throw "FakeNode"; }
  getHeight(): number { throw "FakeNode"; }
  getParent(): Maybe<IProofTreeNode> { throw "FakeNode"; }
  getViewChildren(): IProofTreeNode[] { throw "FakeNode"; }
  getWidth(): number { throw "FakeNode"; }
  isSolved(): boolean { throw "FakeNode"; }
}
