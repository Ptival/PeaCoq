let userTacticsGroupName = "PeaCoq user tactics";

class TacticGroupNode extends ProofTreeNode {
  name: string;
  span: JQuery;
  tacticIndex: number;
  tactics: Tactic[];

  constructor(
    proofTree: ProofTree,
    parent: GoalNode,
    name: string
    ) {
    super(proofTree, parent);
    this.name = name;
    this.tactics = [];
    this.tacticIndex = 0;
  }

  getFocusedChild(): GoalNode {
    let viewChildren = this.getViewChildren();
    if (viewChildren.length === 0) { return undefined; }
    return viewChildren[this.tactics[this.tacticIndex].goalIndex];
  }

  getFocusedTactic(): Tactic {
      if (this.tactics.length === 0) { return undefined; }
      return this.tactics[this.tacticIndex];
  }

  getTactics(): Tactic[] {
    return this.tactics;
  }

  getViewChildren(): GoalNode[] {
    if (this.isSolved) { return []; }
    if (this.tactics.length === 0) { return []; }
    let focusedTactic = this.tactics[this.tacticIndex];
    return focusedTactic.goals;
  }

  nodeWidth(): number { return this.proofTree.tacticWidth; }

  shiftNextInGroup() {
    if (this.tacticIndex < this.tactics.length - 1) {
      this.tacticIndex++;
      //asyncLog("NEXTGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]));
      this.proofTree.update();
    }
  }

  shiftPrevInGroup() {
    if (this.tacticIndex > 0) {
      this.tacticIndex--;
      //asyncLog("PREVGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]));
      this.proofTree.update();
    }
  }

}
