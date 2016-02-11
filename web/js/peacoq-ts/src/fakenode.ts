class FakeNode extends ProofTreeNode {
  constructor() {
    super(undefined, undefined);
  }

  getFocusedChild(): ProofTreeNode { throw "FakeNode"; }
  getViewChildren(): ProofTreeNode[] { throw "FakeNode"; }
  nodeWidth(): number { throw "FakeNode"; }
}
