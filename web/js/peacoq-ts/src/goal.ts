export class Goal {
  goalId: number;
  goalHyp: string[];
  goalCcl: string;

  constructor(g: [string, string[], string]) {
    this.goalId = + g[0];
    this.goalHyp = _(g[1]).map(unbsp).value();
    this.goalCcl = unbsp(g[2]);
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
