let userTacticsGroupName = "PeaCoq user tactics";

class TacticGroupNode extends ProofTreeNode {
  name: string;
  parent: GoalNode;
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
    this.parent = parent;
    this.tactics = [];
    this.tacticIndex = 0;
  }

  getAllDescendants() {
    let children: GoalNode[] = _(this.tactics).map((t) => t.goals).flatten<GoalNode>().value();
    let descendants = _(children).map((c) => c.getAllDescendants()).flatten<ProofTreeNode>().value();
    return [].concat(children, descendants);
  }

  getAllGoalDescendants() {
    let children: GoalNode[] = _(this.tactics).map((t) => t.goals).flatten<GoalNode>().value();
    let descendants = _(children).map((c) => c.getAllGoalDescendants()).flatten<GoalNode>().value();
    return [].concat(children, descendants);
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

  nodeWidth(): number { return this.proofTree.getTacticWidth(); }

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
