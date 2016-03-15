let userTacticsGroupName = "PeaCoq user tactics";

class TacticGroupNode extends ProofTreeNode {
  isProcessed: boolean;
  name: string;
  // do not use parent, D3 will overwrite
  private parentGoal: GoalNode;
  span: JQuery;
  tacticIndex: number;
  tactics: Tactic[];

  constructor(
    proofTree: ProofTree,
    parent: GoalNode,
    name: string
  ) {
    super(proofTree, just(parent));
    this.isProcessed = false;
    this.name = name;
    this.parentGoal = parent;
    this.tactics = [];
    this.tacticIndex = 0;
  }

  click() {
    alert("TODO: click");
  }

  getAllDescendants(): ProofTreeNode[] {
    let children: GoalNode[] = _(this.tactics).map((t) => t.goals).flatten<GoalNode>().value();
    let descendants: ProofTreeNode[] = _(children).map((c) => c.getAllDescendants()).flatten<ProofTreeNode>().value();
    return [].concat(children, descendants);
  }

  getAllGoalDescendants(): GoalNode[] {
    let children: GoalNode[] = _(this.tactics).map((t) => t.goals).flatten<GoalNode>().value();
    let descendants: GoalNode[] = _(children).map((c) => c.getAllGoalDescendants()).flatten<GoalNode>().value();
    return [].concat(children, descendants);
  }

  getFocusedChild(): Maybe<ProofTreeNode> {
    let viewChildren: ProofTreeNode[] = this.getViewChildren();
    if (viewChildren.length === 0) { return nothing(); }
    return just(viewChildren[this.tactics[this.tacticIndex].goalIndex]);
  }

  getFocusedTactic(): Maybe<Tactic> {
    return (
      this.tactics.length === 0
        ? nothing()
        : just(this.tactics[this.tacticIndex])
    );
  }

  getGoalAncestor(): Maybe<GoalNode> { return just(this.parentGoal); }

  getHeight(): number {
    let node = this.getHTMLElement();
    let rect = (<HTMLElement>node.firstChild).getBoundingClientRect();
    return Math.ceil(rect.height);
  }

  getParent(): Maybe<GoalNode> { return just(this.parentGoal); }

  getParentGoal(): GoalNode { return this.parentGoal; }

  getTactics(): Tactic[] {
    return this.tactics;
  }

  getViewChildren(): GoalNode[] {
    if (this.isSolved()) { return []; }
    if (this.tactics.length === 0) { return []; }
    let focusedTactic = this.tactics[this.tacticIndex];
    return focusedTactic.goals;
  }

  getWidth(): number {
    return this.proofTree.getTacticWidth();
  }

  isSolved(): boolean {
    return this.getFocusedTactic().caseOf({
      nothing: () => false,
      just: (t) => this.isProcessed && t.isSolved(),
    });
  }

  nodeWidth(): number { return this.proofTree.getTacticWidth(); }

  onChildSolvedAndUnfocused(sid: number): void {
    let focusedTactic = fromJust(this.getFocusedTactic());
    let unsolved = _(focusedTactic.goals)
      .find(function(elt) {
        return !elt.isSolved();
      })
      ;
    if (unsolved === undefined) {
      this.onSolved(sid);
    } else {
      unsolved.stateIds.push(sid);
      this.proofTree.curNode = unsolved;
      //this.proofTree.refreshTactics();
      this.proofTree.update();
    }
  }

  onSolved(sid: number): void {
    let self = this;
    this.proofTree.curNode = this.parentGoal;
    this.proofTree.update()
      .then(function() {
        self.parentGoal.onChildSolved(sid);
      })
      ;
  }

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
