import * as _ from "lodash"

export class Tactic implements ITactic {
  // addReturn: AddReturn
  public goalIndex: number

  constructor(
    public tactic: string,
    public parentGroup: ITacticGroupNode,
    public goals: IGoalNode[]
  ) {
    // this.addReturn = waiting.addReturn
    this.goalIndex = 0

    // const focusedBefore = getResponseFocused(parent.parent.response)
    // const focusedAfter = getResponseFocused(response)

    // const unfocusedBefore = getResponseUnfocused(parent.parent.response)
    // const unfocusedAfter = getResponseUnfocused(response)

    // const remainingSubgoals
    /*
    if (_.isEqual(unfocusedAfter, unfocusedBefore)) {
      if (focusedBefore.length > 1
        && focusedAfter[0].gId === focusedBefore[1].gId) {
        remainingSubgoals = []
      } else {
        const focusDelta = focusedAfter.length - focusedBefore.length
        remainingSubgoals = response.rGoals.focused.slice(0, focusDelta + 1)
      }
    } else {
      remainingSubgoals = []
    }
    //console.log(tactic, focusDelta, parent.parent.response, response, remainingSubgoals)
    this.goals = _(remainingSubgoals).map(function(goal, index) {
      return new GoalNode(proofTree, this, response)
    }).value()
    */
  }

  public focus(): void {
    const tacticIndex = _.findIndex(this.parentGroup.tactics, t => t.tactic === this.tactic)
    if (tacticIndex === -1) { debugger }
    this.parentGroup.tacticIndex = tacticIndex
    this.parentGroup.focus()
  }

  public getFocusedGoal(): Maybe<IGoalNode> {
    if (this.goals.length === 0) { return nothing<IGoalNode>() }
    return just(this.goals[this.goalIndex])
  }

  public isSolved(): boolean {
    return _.every(this.goals, g => g.isSolved())
  }

}
