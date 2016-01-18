class FakeNode extends ProofTreeNode {
  constructor() {
    super(undefined, undefined);
    this.isFake = true;
  }

  getFocusedChild(): ProofTreeNode { throw "FakeNode"; }
  getViewChildren(): ProofTreeNode[] { throw "FakeNode"; }
  isTacticish(): boolean { return false; }
  nodeWidth(): number { throw "FakeNode"; }
}
