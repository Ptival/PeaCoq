type PeaCoqContext = IPeaCoqGoal[];

interface IPeaCoqGoal {
  getHTML(): string;
}

interface PeaCoqHyp {
  name: string;
  maybeTerm: Maybe<IConstrExpr>;
  type: IConstrExpr;
}
