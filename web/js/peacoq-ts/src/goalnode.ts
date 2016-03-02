class GoalNode extends ProofTreeNode {
  // DO NOT USE "children" AS D3 WILL OVERWRITE
  closedBraces: number;
  //gid: number;
  goal: PeaCoqGoal;
  goals: Goals;
  html: JQuery;
  nodeHTML: JQuery;
  //goalString: string;
  //goalTerm: string;
  //hyps: Hypothesis[];
  //ndx: number;
  openBraces: number;
  //parentTactic: TacticNode;
  // DO NOT USE "parent" AS D3 WILL OVERWRITE
  private parentGroup: Maybe<TacticGroupNode>;
  solved: boolean;
  stateIds: number[];
  tacticGroups: TacticGroupNode[];
  tacticIndex: number;

  constructor(proofTree: ProofTree, parent: Maybe<TacticGroupNode>, goals: Goals, goal: PeaCoqGoal) {
    super(proofTree, parent);

    this.closedBraces = 0;
    this.goal = goal;
    this.goals = goals;
    this.html = $("<div>")
      .attr("id", _.uniqueId())
      .append(this.goal.getHTML())
      ;
    this.openBraces = 0;
    this.parentGroup = parent;
    this.solved = false;
    this.stateIds = [];
    this.tacticGroups = [];
    this.tacticIndex = 0;

    if (proofTree.rootNode === undefined) {
      proofTree.rootNode = this;
    }
  }

  click(): void { return; }

  getAllDescendants(): ProofTreeNode[] {
    let children: TacticGroupNode[] = this.tacticGroups;
    let descendants: ProofTreeNode[] = _(children).map((c) => c.getAllDescendants()).flatten<ProofTreeNode>().value();
    return [].concat(children, descendants);
  }

  getAllGoalDescendants(): GoalNode[] {
    let children: TacticGroupNode[] = this.tacticGroups;
    let descendants: GoalNode[] = _(children).map((c) => c.getAllGoalDescendants()).flatten<GoalNode>().value();
    let result: GoalNode[] = [this];
    return result.concat(descendants);
  }

  getFocusedChild(): Maybe<ProofTreeNode> {
    let viewChildren: ProofTreeNode[] = this.getViewChildren();
    if (viewChildren.length === 0) { return nothing(); }
    return just(viewChildren[this.tacticIndex]);
  }

  getFocusedTacticGroup(): TsMonad.Maybe<TacticGroupNode> {
    let nonEmptyTacticGroups: TacticGroupNode[] = _(this.tacticGroups)
      .filter(function(group) { return (group.tactics.length > 0); })
      .value()
      ;
    if (nonEmptyTacticGroups.length === 0) { return TsMonad.Maybe.nothing(); }
    return TsMonad.Maybe.just(nonEmptyTacticGroups[this.tacticIndex]);
  }

  getGoalAncestors(): GoalNode[] {
    return this.getGrandParent().caseOf({
      nothing: () => [this],
      just: (gp) => [].concat([this], gp.getGoalAncestors()),
    });
  }

  getGrandParent(): Maybe<GoalNode> {
    return this.parentGroup.caseOf({
      nothing: () => nothing(),
      just: (p: TacticGroupNode) => just(p.parent),
    });
  }

  getParent(): Maybe<TacticGroupNode> { return this.parentGroup; }

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
    if (this.isSolved()) { return []; }
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

  isSolved(): boolean {
    let focusedTacticGroup = this.getFocusedTacticGroup();
    return this.getFocusedTacticGroup().caseOf({
      nothing: () => false,
      just: (tg) => tg.isSolved(),
    });
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
      this.parentGroup.caseOf({
        nothing: () => {
          if (autoLayout) {
            //proofTreeQueryWish('Qed.');
          }
        },
        just: (p) => p.onChildSolvedAndUnfocused(),
      });
    } else if (autoLayout) {
      //proofTreeQueryWish('}');
    }
  }

  nodeWidth() {
    return this.proofTree.getGoalWidth();
  }

}
