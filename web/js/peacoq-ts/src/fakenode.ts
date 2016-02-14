class FakeNode extends ProofTreeNode {
  constructor() {
    super(undefined, undefined);
  }

  getAllDescendants(): ProofTreeNode[] { throw "FakeNode"; }
  getAllGoalDescendants(): GoalNode[] { throw "FakeNode"; }
  getFocusedChild(): ProofTreeNode { throw "FakeNode"; }
  getViewChildren(): ProofTreeNode[] { throw "FakeNode"; }
  nodeWidth(): number { throw "FakeNode"; }
}
