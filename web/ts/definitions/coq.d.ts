interface CoqLocation {
  fName: string;
  lineNb: number;
  bolPos: number;
  lineNbLast: number;
  bolPosLast: number;
  bp: number;
  ep: number;
}
type EditId = number;
type StateId = number;
type GlobLevel = IGlobSortGen<LevelInfo>;
type GlobSort = IGlobSortGen<SortInfo>;
type InstanceExpr = Array<GlobLevel>;
type LevelInfo = Maybe<string>;
type Located<T> = [CoqLocation, T];
type SortInfo = string[];

interface INewTip {}
interface IFocus {}
interface IUnfocus {}

interface AddReturn {
  stateId: number;
  eitherNullStateId: number;
  output: string;
}

interface IConstrExpr { }

declare const enum EditOrState {
  Edit,
  State,
}

interface IFeedback<C extends IFeedbackContent> {
  editOrState: EditOrState;
  editOrStateId: number;
  feedbackContent: C;
  routeId: RouteId;
}

interface IFeedbackContent { }

declare namespace IFeedbackContent {
  interface IAddedAxiom extends IFeedbackContent { }
  interface IFileDependency extends IFeedbackContent { }
  interface IFileLoaded extends IFeedbackContent { }
  interface IMessage<L extends IMessageLevel> extends IFeedbackContent {
    level: L;
    location: Maybe<CoqLocation>;
    message: string;
  }
  interface IProcessed extends IFeedbackContent { }
  interface IProcessingIn extends IFeedbackContent { }
  interface IWorkerStatus extends IFeedbackContent { }
}

interface IMessageLevel { }

declare namespace IMessageLevel {
  interface IDebug extends IMessageLevel { }
  interface IError extends IMessageLevel { }
  interface IInfo extends IMessageLevel { }
  interface INotice extends IMessageLevel { }
  interface IWarning extends IMessageLevel { }
}

type MessageFeedback<L> = IFeedback<IFeedbackContent.IMessage<L>>;

type DebugMessageFeedback = MessageFeedback<IMessageLevel.IDebug>;
type ErrorMessageFeedback = MessageFeedback<IMessageLevel.IError>;
type InfoMessageFeedback = MessageFeedback<IMessageLevel.IInfo>;
type NoticeMessageFeedback = MessageFeedback<IMessageLevel.INotice>;
type WarningMessageFeedback = MessageFeedback<IMessageLevel.IWarning>;

interface IGlobSortGen<T> { }

interface IGoal {
  goalId: number;
  goalHyp: string[];
  goalCcl: string;
}

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
