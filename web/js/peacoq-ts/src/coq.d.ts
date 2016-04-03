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
