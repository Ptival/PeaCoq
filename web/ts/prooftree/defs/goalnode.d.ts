interface IGoalNode extends IProofTreeNode {
  // constructor(
  //   IProofTree: IProofTree, parent: Maybe<ITacticGroupNode>, goals: IGoals, goal: IPeaCoqGoal
  // );
  context: PeaCoqContext;
  fgIndex: number;
  html: JQuery;
  // stateIds: number[];
  tacticGroups: ITacticGroupNode[];
  addStateId(s: StateId): void;
  getGoalAncestors(): IGoalNode[];
  getTactics(): ITactic[];
  getStateIds(): StateId[];
  onChildSolved(sid: number): void;
  onSolved(sid: number): void;
  removeStateIds(sids: StateId[]): void;
}
