export class Tactic {
  //addReturn: AddReturn;
  goalIndex: number;

  constructor(
    public tactic: string,
    public parentGroup: ITacticGroupNode,
    public goals: IGoalNode[]
  ) {
    //this.addReturn = waiting.addReturn;
    this.goalIndex = 0;

    //let focusedBefore = getResponseFocused(parent.parent.response);
    //let focusedAfter = getResponseFocused(response);

    //let unfocusedBefore = getResponseUnfocused(parent.parent.response);
    //let unfocusedAfter = getResponseUnfocused(response);

    //let remainingSubgoals;
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
  }

  focus(): void {
    const tacticIndex = _.findIndex(this.parentGroup.tactics, t => t.tactic === this.tactic);
    if (tacticIndex === -1) { debugger; }
    this.parentGroup.tacticIndex = tacticIndex;
    this.parentGroup.focus();
  }

  isSolved(): boolean {
    return _.every(this.goals, g => g.isSolved());
  }

}
