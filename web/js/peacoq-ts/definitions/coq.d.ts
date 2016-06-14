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

interface IFeedback<C extends IFeedbackContent> {
  editOrState: string;
  editOrStateId: number;
  feedbackContent: C;
}

interface IFeedbackContent { }

declare namespace FeedbackContent {
  interface IAddedAxiom extends IFeedbackContent { }
  interface IErrorMsg extends IFeedbackContent {
    message: string;
  }
  interface IFileDependency extends IFeedbackContent { }
  interface IFileLoaded extends IFeedbackContent { }
  interface IProcessed extends IFeedbackContent { }
  interface IProcessingIn extends IFeedbackContent { }
  interface IWorkerStatus extends IFeedbackContent { }
}

interface IGlobSortGen<T> { }

interface IGoal { }

interface BeforeAfter<T> {
  before: T[];
  after: T[];
}

interface IGoals<T> {
  fgGoals: T[];
  bgGoals: BeforeAfter<T>[];
  shelvedGoals: T[];
  givenUpGoals: T[];
}

interface IMessage {
  content: string;
  level: IMessageLevel;
  // display(): void;
}

interface IMessageLevel {
}

interface IStatus {
  // statusPath: string[];
  statusProofName: string;
  statusAllProofs: string;
  // statusProofNum: number;
}

interface ErrorLocation {
  startPos: number;
  stopPos: number;
}

interface IValueFail {
  location: Maybe<ErrorLocation>;
  message: string;
  stateId: number;
}
