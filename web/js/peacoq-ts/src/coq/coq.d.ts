type CoqLocation = [number, number];

interface IGlobSortGen<T> {

}

type LevelInfo = Maybe<string>;
type GlobLevel = IGlobSortGen<LevelInfo>;

type SortInfo = string[];
type GlobSort = IGlobSortGen<SortInfo>;

type InstanceExpr = Array<GlobLevel>;

type Located<T> = [CoqLocation, T];

interface IConstrExpr {

}

interface IFeedbackContent {
}

interface IFeedback {
  editOrState: string;
  editOrStateId: number;
  feedbackContent: IFeedbackContent;
}

interface IMessage {
  content: string;
  level: IMessageLevel;
  display(): void;
}

interface IMessageLevel {

}

interface IValueFail {
  stateId: number;
}

type AddReturn = {
  stateId: number;
  eitherNullStateId: number;
  output: string;
}
