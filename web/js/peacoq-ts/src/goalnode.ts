class GoalNode extends ProofTreeNode {
  closedBraces: number;
  //gid: number;
  goal: PeaCoqGoal;
  html: JQuery;
  //goalSpan: JQuery;
  //goalString: string;
  //goalTerm: string;
  //hyps: Hypothesis[];
  //ndx: number;
  openBraces: number;
  //parentTactic: TacticNode;
  tacticGroups: TacticGroupNode[];
  tacticIndex: number;

  constructor(proofTree: ProofTree, parent: TacticNode, goal: PeaCoqGoal) {
    super(proofTree, parent);
    this.goal = goal;

    this.html = $("<div>")
      .attr("id", _.uniqueId())
      ;

    this.html.append(
      $("<div>").html(htmlPrintHyps(goal.hyps))
    );

    this.html.append(makeContextDivider());

    this.html.append(
      $("<div>").html(htmlPrintConstrExpr(goal.concl))
    );

    /*
    let goal = goals.fgGoals[0];
    let goalTerm = extractGoal(goal.gGoal);
    this.hyps = _(goal.gHyps).map(extractHypothesis).value();
    this.ndx = index + 1; // used in Focus, Coq uses 1-index
    this.gid = goal.gId;
    this.goalTerm = goalTerm;
    this.goalString = showTermText(goalTerm);
    */
    this.tacticGroups = [
      //
      new TacticGroupNode(proofTree, this, userTacticsGroupName),
    ];
    this.tacticIndex = 0;
    /*
    this.parentTactic = parentTactic;
    */

    this.openBraces = 0;
    this.closedBraces = 0;
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

  getTactics(): TacticNode[] {
    return _(this.tacticGroups)
      .map(function(g) { return g.getTactics(); })
      .flatten<TacticNode>(true)
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

  isTacticish(): boolean { return false; }

  nodeWidth() {
    return this.proofTree.goalWidth;
  }

}
