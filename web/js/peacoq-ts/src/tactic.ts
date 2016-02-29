// class TacticWaiting {
//   addReturn: AddReturn;
//   parentGroup: TacticGroupNode;
//   tactic: string;
//
//   constructor(tactic: string, parentGroup: TacticGroupNode, addReturn: AddReturn) {
//     this.addReturn = addReturn;
//     this.parentGroup = parentGroup;
//     this.tactic = tactic;
//   }
// }

class Tactic {
  //addReturn: AddReturn;
  goalIndex: number;
  goals: GoalNode[];
  parentGroup: TacticGroupNode;
  tactic: string;

  constructor(tactic: string, parentGroup: TacticGroupNode, goals: GoalNode[]) {
    //this.addReturn = waiting.addReturn;
    this.goalIndex = 0;
    this.goals = goals;
    this.parentGroup = parentGroup;
    this.tactic = tactic;

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

  isSolved(): boolean {
    return _.every(this.goals, (g) => g.isSolved());
  }

}
