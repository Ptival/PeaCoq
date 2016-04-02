import { Goal } from "./goal";

type GoalBeforeAfter = {
  before: Goal[];
  after: Goal[];
};

export class Goals {
  fgGoals: Goal[];
  bgGoals: GoalBeforeAfter[];
  shelvedGoals: Goal[];
  givenUpGoals: Goal[];

  constructor(maybeGoals) {
    if (!maybeGoals) {
      this.fgGoals = [];
      this.bgGoals = [];
      this.shelvedGoals = [];
      this.givenUpGoals = [];
    } else {
      this.fgGoals = _(maybeGoals[0]).map(function(g) {
        return new Goal(g);
      }).value();
      this.bgGoals = _(maybeGoals[1]).map(function(ba) {
        return {
          "before": _(ba[0]).map(function(b) { return new Goal(b); }).value(),
          "after": _(ba[1]).map(function(b) { return new Goal(b); }).value(),
        };
      }).value();
      this.shelvedGoals = _(maybeGoals[2]).map(function(g) {
        return new Goal(g);
      }).value();
      this.givenUpGoals = _(maybeGoals[3]).map(function(g) {
        return new Goal(g);
      }).value();
    }
  }

}
