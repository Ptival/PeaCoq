class Tactic {
  goalIndex: number;
  goals: GoalNode[];
  tactic: string;

  constructor(
    proofTree: ProofTree,
    parent: TacticGroupNode,
    tactic: string
    //, response: any
    ) {
    super(proofTree, parent);
    this.tactic = tactic;

    //let focusedBefore = getResponseFocused(parent.parent.response);
    //let focusedAfter = getResponseFocused(response);

    //let unfocusedBefore = getResponseUnfocused(parent.parent.response);
    //let unfocusedAfter = getResponseUnfocused(response);

    let remainingSubgoals;
    /*
    if (_.isEqual(unfocusedAfter, unfocusedBefore)) {
      if (focusedBefore.length > 1
        && focusedAfter[0].gId === focusedBefore[1].gId) {
        remainingSubgoals = [];
      } else {
        let focusDelta = focusedAfter.length - focusedBefore.length;
        remainingSubgoals = response.rGoals.focused.slice(0, focusDelta + 1);
      }
    } else {
      remainingSubgoals = [];
    }
    //console.log(tactic, focusDelta, parent.parent.response, response, remainingSubgoals);
    this.goals = _(remainingSubgoals).map(function(goal, index) {
      return new GoalNode(proofTree, this, response);
    }).value();
    */

    this.goalIndex = 0;
  }

  getFocusedChild() {
    let viewChildren = this.getViewChildren();
    if (viewChildren.length === 0) { return undefined; }
    return viewChildren[this.goalIndex];
  }

  getViewChildren(): GoalNode[] {
    if (this.isSolved) { return []; }
    if (this.goals.length === 0) { return []; }
    // Note: This SHOULD NOT be the current node!
    return this.goals;
  }

  isTacticish(): boolean { return true; }

  nodeWidth(): number { return this.proofTree.tacticWidth; }

}
