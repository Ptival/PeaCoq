class FakeNode extends ProofTreeNode {
  constructor() {
    super(undefined, undefined);
    this.isFake = true;
  }

  getFocusedChild(): ProofTreeNode { throw "FakeNode"; }
  getViewChildren(): ProofTreeNode[] { throw "FakeNode"; }
  nodeWidth(): number { throw "FakeNode"; }
}
