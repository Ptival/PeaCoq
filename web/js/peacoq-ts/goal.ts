export class Goal implements IGoal {
  goalId: number;
  goalHyp: string[];
  goalCcl: string;

  constructor(o: any) {
    this.goalId = + o.goal_id;
    this.goalHyp = _(o.goal_hyp).map(unbsp).value();
    this.goalCcl = unbsp(o.goal_ccl);
  }

  toString(): string {
    let res = "";//"Goal " + this.goalId + "\n\n";
    _(this.goalHyp).each(function(h) {
      res += h + "\n";
    });
    _(_.range(80)).each(function() { res += '-'; });
    res += "\n" + this.goalCcl;
    return res;
  }

}
