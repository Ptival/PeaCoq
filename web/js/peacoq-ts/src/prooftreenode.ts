
abstract class ProofTreeNode {
  cX: number;
  cX0: number;
  cY: number;
  cY0: number;
  depth: number;
  height: number;
  id: string;
  isSolved: boolean;
  label: string;
  parent: ProofTreeNode;
  proofTree: ProofTree;
  response: any; // TODO: remove this
  width: number;
  x: number;
  x0: number;
  y: number;
  y0: number;

  constructor(proofTree: ProofTree, parent: ProofTreeNode) {
    this.id = _.uniqueId();
    this.proofTree = proofTree;
    this.parent = parent;
    this.depth = (parent === undefined) ? 0 : parent.depth + 1;
    this.isSolved = false;
  }

  abstract getFocusedChild(): ProofTreeNode;

  abstract getViewChildren(): ProofTreeNode[];

  getViewGrandChildren(): ProofTreeNode[] {
    return (
      _(this.getViewChildren())
        .map(function(e) { return e.getViewChildren(); })
        .flatten<ProofTreeNode>(true)
        .value()
      );
  }

  isCurNodeAncestor() {
    let curNode = this.proofTree.curNode;
    let common = this.proofTree.commonAncestor(curNode, this);
    return this.id === common.id;
  }

  abstract nodeWidth(): number;

}
