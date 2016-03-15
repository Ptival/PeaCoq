class FakeNode extends ProofTreeNode {
  constructor(p: ProofTree, parent: ProofTreeNode) {
    super(p, just(parent));
  }

  click(): void { throw "FakeNode"; }
  getAllDescendants(): ProofTreeNode[] { throw "FakeNode"; }
  getAllGoalDescendants(): GoalNode[] { throw "FakeNode"; }
  getFocusedChild(): Maybe<ProofTreeNode> { throw "FakeNode"; }
  getGoalAncestor(): Maybe<GoalNode> { throw "FakeNode"; }
  getHeight(): number { throw "FakeNode"; }
  getParent(): Maybe<ProofTreeNode> { throw "FakeNode"; }
  getViewChildren(): ProofTreeNode[] { throw "FakeNode"; }
  getWidth(): number { throw "FakeNode"; }
  isSolved(): boolean { throw "FakeNode"; }
  nodeWidth(): number { throw "FakeNode"; }
}
