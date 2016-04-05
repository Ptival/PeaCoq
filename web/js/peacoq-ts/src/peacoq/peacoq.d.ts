type PeaCoqContext = IPeaCoqGoal[];

interface IPeaCoqGoal {
  getHTML(): JQuery;
}

interface PeaCoqHyp {
  name: string;
  maybeTerm: Maybe<IConstrExpr>;
  type: IConstrExpr;
}
