import { Goal } from "./goal";

export class Goals implements IGoals {
  fgGoals: Goal[];
  bgGoals: GoalBeforeAfter[];
  shelvedGoals: Goal[];
  givenUpGoals: Goal[];

  constructor(maybeGoals: any) {
    if (!maybeGoals) {
      this.fgGoals = [];
      this.bgGoals = [];
      this.shelvedGoals = [];
      this.givenUpGoals = [];
    } else {
      this.fgGoals = _(maybeGoals[0]).map(function(g: any) {
        return new Goal(g);
      }).value();
      this.bgGoals = _(maybeGoals[1]).map(function(ba: any) {
        return {
          "before": _(ba[0]).map(function(b: any) { return new Goal(b); }).value(),
          "after": _(ba[1]).map(function(b: any) { return new Goal(b); }).value(),
        };
      }).value();
      this.shelvedGoals = _(maybeGoals[2]).map(function(g: any) {
        return new Goal(g);
      }).value();
      this.givenUpGoals = _(maybeGoals[3]).map(function(g: any) {
        return new Goal(g);
      }).value();
    }
  }

}
