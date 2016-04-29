type CoqLocation = [number, number];
type GlobLevel = IGlobSortGen<LevelInfo>;
type GlobSort = IGlobSortGen<SortInfo>;
type InstanceExpr = Array<GlobLevel>;
type LevelInfo = Maybe<string>;
type Located<T> = [CoqLocation, T];
type SortInfo = string[];

interface AddReturn {
  stateId: number;
  eitherNullStateId: number;
  output: string;
}

interface IConstrExpr { }

interface IFeedback {
  editOrState: string;
  editOrStateId: number;
  feedbackContent: IFeedbackContent;
}

interface IFeedbackContent { }

interface IGlobSortGen<T> { }

interface IGoal { }

interface GoalBeforeAfter {
  before: IGoal[];
  after: IGoal[];
}

interface IGoals {
  fgGoals: IGoal[];
  bgGoals: GoalBeforeAfter[];
  shelvedGoals: IGoal[];
  givenUpGoals: IGoal[];
}

interface IMessage {
  content: string;
  level: IMessageLevel;
  display(): void;
}

interface IMessageLevel { }

interface IStatus {
  // statusPath: string[];
  statusProofName: string;
  statusAllProofs: string;
  // statusProofNum: number;
}

interface IValueFail {
  stateId: number;
}
