import { Goal } from "../goal";
import * as Goals from "../goals";
import { PeaCoqGoal } from "../peacoq-goal";
import { walkJSON } from "../peacoq/json";

export function create(rawContext): PeaCoqContext {
  const safeContents = rawContext
    .replace(/\n/g, "\\n")
    .replace(/\r/g, "\\r")
    .replace(/\t/g, "\\t")
    .replace(/\f/g, "\\f");
  const c: IGoals<any> = JSON.parse(safeContents);
  const context: PeaCoqContext = Goals.apply(
    c => {
      const pp: any = walkJSON(c.ppgoal);
      return {
        goal: new Goal(c.goal),
        ppgoal: new PeaCoqGoal(pp.hyps, pp.concl),
      };
    },
    c
  );
  return context;
}

export function getAllGoals(c: PeaCoqContext): IGoal[] {
  return [].concat(
    c.fgGoals,
    c.bgGoals.map(e => e.before),
    c.bgGoals.map(e => e.after),
    c.shelvedGoals,
    c.givenUpGoals,
  ).map(e => e.goal);
}

export function isEqual(context1: PeaCoqContext, context2: PeaCoqContext): boolean {
  // we compare only the goal field, because the ppgoal field gets injected with HTML and stuff...
  return _.isEqual(getAllGoals(context1), getAllGoals(context2));
}
