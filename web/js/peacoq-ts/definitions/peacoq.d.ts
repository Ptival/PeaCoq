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
    coqExn$:  Rx.Observable<Sertop.IAnswer<Sertop.ICoqExn>>;
    stmAdded$: Rx.Observable<Sertop.IAnswer<Sertop.IStmAdded>>;
  }
  feedback$s: {
  //   addedAxiom$: Rx.Observable<IFeedback<FeedbackContent.IAddedAxiom>>;
  //   errorMsg$: Rx.Observable<IFeedback<FeedbackContent.IErrorMsg>>;
  //   fileDependency$: Rx.Observable<IFeedback<FeedbackContent.IFileDependency>>;
  //   fileLoaded$: Rx.Observable<IFeedback<FeedbackContent.IFileLoaded>>;
    processed$: Rx.Observable<IFeedback<FeedbackContent.IProcessed>>;
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
