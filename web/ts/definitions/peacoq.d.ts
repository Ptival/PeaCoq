declare const enum PeaCoqMessageLevel {
  Default,
  Danger,
  Info,
  Success,
  Warning,
}

interface PeaCoqContextElement {
  goal: IGoal;
  ppgoal: IPeaCoqGoal;
}

type PeaCoqContext = IGoals<PeaCoqContextElement>

interface IPeaCoqGoal {
  hyps: PeaCoqHyp[];
  concl: IConstrExpr;
  getHTML(): JQuery;
}

interface PeaCoqHyp {
  name: string;
  maybeTerm: Maybe<IConstrExpr>;
  type: IConstrExpr;
}
