class FakeNode extends ProofTreeNode {
  constructor() {
    super(undefined, undefined);
  }

  click(): void { throw "FakeNode"; }
  getAllDescendants(): ProofTreeNode[] { throw "FakeNode"; }
  getAllGoalDescendants(): GoalNode[] { throw "FakeNode"; }
  getFocusedChild(): Maybe<ProofTreeNode> { throw "FakeNode"; }
  getParent(): Maybe<ProofTreeNode> { throw "FakeNode"; }
  getViewChildren(): ProofTreeNode[] { throw "FakeNode"; }
  isSolved(): boolean { throw "FakeNode"; }
  nodeWidth(): number { throw "FakeNode"; }
}
