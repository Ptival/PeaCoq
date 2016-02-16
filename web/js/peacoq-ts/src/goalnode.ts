class GoalNode extends ProofTreeNode {
  closedBraces: number;
  //gid: number;
  goal: PeaCoqGoal;
  html: JQuery;
  nodeHTML: JQuery;
  //goalString: string;
  //goalTerm: string;
  //hyps: Hypothesis[];
  //ndx: number;
  openBraces: number;
  //parentTactic: TacticNode;
  parent: TacticGroupNode;
  solved: boolean;
  stateIds: number[];
  tacticGroups: TacticGroupNode[];
  tacticIndex: number;

  constructor(proofTree: ProofTree, parent: TacticGroupNode, goal: PeaCoqGoal) {
    super(proofTree, parent);

    this.closedBraces = 0;
    this.goal = goal;
    this.html = $("<div>")
      .attr("id", _.uniqueId())
      .append(this.goal.getHTML())
      ;
    this.openBraces = 0;
    this.parent = parent;
    this.solved = false;
    this.stateIds = [];
    this.tacticGroups = [];
    this.tacticIndex = 0;

    if (proofTree.rootNode === undefined) {
      proofTree.rootNode = this;
    }
  }

  getAllDescendants() {
    let children = this.tacticGroups;
    let descendants = _(children).map((c) => c.getAllDescendants()).flatten<ProofTreeNode>().value();
    return [].concat(children, descendants);
  }

  getAllGoalDescendants() {
    let children = this.tacticGroups;
    let descendants = _(children).map((c) => c.getAllGoalDescendants()).flatten<GoalNode>().value();
    return [].concat(children, descendants);

  }

  getFocusedChild() {
    let viewChildren = this.getViewChildren();
    if (viewChildren.length === 0) { return undefined; }
    return viewChildren[this.tacticIndex];
  }

  getFocusedTacticGroup(): TacticGroupNode {
    let nonEmptyTacticGroups = _(this.tacticGroups)
      .filter(function(group) { return (group.tactics.length > 0); })
      .value()
      ;
    if (nonEmptyTacticGroups.length === 0) { return undefined; }
    return nonEmptyTacticGroups[this.tacticIndex];
  }

  getGoalAncestors(): GoalNode[] {
    if (this.parent === undefined) { return [this]; }
    let grandparent = this.parent.parent;
    assert(grandparent instanceof GoalNode, "getGoalAncestors: grandparent instanceof GoalNode");
    let rec = (<GoalNode>grandparent).getGoalAncestors();
    rec.unshift(this);
    return rec;
  }

  getParent(): ProofTreeNode { return this.parent; }

  getTactics(): Tactic[] {
    return _(this.tacticGroups)
      .map(function(g) { return g.getTactics(); })
      .flatten<Tactic>(true)
      .value()
      ;
  }

  /*
   * [getViewChildren] returns the children of the considered node in the current
   * view. If the node is collapsed, it needs to have one child if it is an
   * ancestor of the current node, so that the current node is reachable.
   */
  getViewChildren(): TacticGroupNode[] {
    if (this.isSolved) { return []; }
    let nonEmptyTacticGroups = _(this.tacticGroups)
      .filter(function(group) { return (group.tactics.length > 0); })
      .value()
      ;
    if (nonEmptyTacticGroups.length === 0) { return []; }
    if (this.proofTree.isCurNode(this)) {
      return nonEmptyTacticGroups;
    } else if (this.isCurNodeAncestor()) {
      return [nonEmptyTacticGroups[this.tacticIndex]];
    } else {
      return [];
    }
  }

  onChildSolved(): void {
    let self = this;
    this.solved = true;
    this.proofTree.update()
      .then(function() {
        self.onSolved();
      })
      ;
  }

  onSolved(): void {
    if (this.openBraces === this.closedBraces) {
      if (hasParent(this)) {
        this.parent.onChildSolvedAndUnfocused();
      } else if (autoLayout) {
        //proofTreeQueryWish('Qed.');
      }
    } else if (autoLayout) {
      //proofTreeQueryWish('}');
    }
  }

  nodeWidth() {
    return this.proofTree.getGoalWidth();
  }

}
