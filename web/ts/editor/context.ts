import { Goal } from "../coq/goal";
import * as Goals from "../coq/goals";
import { PeaCoqGoal } from "../peacoq/goal";
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
  return ([] as PeaCoqContextElement[]).concat(
    c.fgGoals,
    _.flatten(c.bgGoals.map(e => e.before)),
    _.flatten(c.bgGoals.map(e => e.after)),
    c.shelvedGoals,
    c.givenUpGoals,
  ).map(e => e.goal);
}

export function isEqual(context1: PeaCoqContext, context2: PeaCoqContext): boolean {
  // we compare only the goal field, because the ppgoal field gets injected with HTML and stuff...
  // we also must avoid comparing goal field, because each goal has an id, and
  // some tactics produce the same context with a fresh id, so we compare
  // goalHyp and goalCcl fields only
  return _.every(
    _.zipWith(
      getAllGoals(context1), getAllGoals(context2),
      (g1, g2) =>
        g1 !== undefined && g2 !== undefined // in case lengths differ
        && _.isEqual(g1.goalHyp, g2.goalHyp)
        && _.isEqual(g1.goalCcl, g2.goalCcl)
    )
  );
  // isEqualWith(getAllGoals(context1), getAllGoals(context2));
}
