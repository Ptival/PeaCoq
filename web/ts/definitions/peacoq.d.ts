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

interface CoqtopOutputStreams {
  // all inputs/outputs
  // input$: Rx.Observable<ICoqtopInput>;
  // io$: Rx.Observable<ICoqtopOutput<ICoqtopInput, any>>;
  // error$: Rx.Observable<ValueFail>;
  answer$s: {
    completed$: Rx.Observable<ISertop.IAnswer<ISertop.ICompleted>>;
    coqExn$: Rx.Observable<ISertop.IAnswer<ISertop.ICoqExn>>;
    stmAdded$: Rx.Observable<ISertop.IAnswer<ISertop.IStmAdded>>;
    stmCanceled$: Rx.Observable<ISertop.IAnswer<ISertop.IStmCanceled>>;
  }
  feedback$s: {
    message$s: {
      debug$: Rx.Observable<DebugMessageFeedback>;
      error$: Rx.Observable<ErrorMessageFeedback>;
      info$: Rx.Observable<InfoMessageFeedback>;
      notice$: Rx.Observable<NoticeMessageFeedback>;
      warning$: Rx.Observable<WarningMessageFeedback>;
    },
  //   addedAxiom$: Rx.Observable<IFeedback<FeedbackContent.IAddedAxiom>>;
  //   fileDependency$: Rx.Observable<IFeedback<FeedbackContent.IFileDependency>>;
  //   fileLoaded$: Rx.Observable<IFeedback<FeedbackContent.IFileLoaded>>;
    processed$: Rx.Observable<IFeedback<IFeedbackContent.IProcessed>>;
  //   processingIn$: Rx.Observable<IFeedback<FeedbackContent.IProcessingIn>>;
  };
  // feedback$: Rx.Observable<IFeedback<IFeedbackContent>>;
  // // response$: Rx.Observable<ICoqtopResponse<ICoqtopInput, any>>;
  // message$: Rx.Observable<IMessage>;
  // // stateId$: Rx.Observable<number>;
  // valueFail$: Rx.Observable<IValueFail>;
  // // Only contains responses from ValueGood
  // valueGood$s: {
  //   add$: Rx.Observable<ICoqtopOutput<CoqtopInput.IAddPrime, CoqtopOutput.AddPrime>>;
  //   editAt$: Rx.Observable<ICoqtopOutput<CoqtopInput.IEditAt, CoqtopOutput.EditAt>>;
  // }
}
