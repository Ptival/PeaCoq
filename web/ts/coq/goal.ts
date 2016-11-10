import * as _ from "lodash"

export class Goal implements IGoal {
  public goalId: number
  public goalHyp: string[]
  public goalCcl: string

  // TODO: make the fields parameters of constructor and move this logic
  // in the callees
  constructor(o: any) {
    this.goalId = + o.goal_id
    this.goalHyp = _(o.goal_hyp).map(unbsp).value()
    this.goalCcl = unbsp(o.goal_ccl)
  }

  public toString(): string {
    let res = "" // "Goal " + this.goalId + "\n\n"
    this.goalHyp.forEach(h => {
      res += h + "\n"
    })
    _.range(80).forEach(() => { res += "-" })
    res += "\n" + this.goalCcl
    return res
  }

}
