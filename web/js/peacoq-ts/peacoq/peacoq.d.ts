interface PeaCoqContextElement {
  goal: IGoal;
  ppgoal: IPeaCoqGoal;
}

type PeaCoqContext = IGoals<PeaCoqContextElement>

interface IPeaCoqGoal {
  getHTML(): JQuery;
}

interface PeaCoqHyp {
  name: string;
  maybeTerm: Maybe<IConstrExpr>;
  type: IConstrExpr;
}
