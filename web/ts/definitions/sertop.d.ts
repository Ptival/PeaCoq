interface ToSexp {
    toSexp(): string
}

interface CoqtopOutputStreams {
    // all inputs/outputs
    // input$: Rx.Observable<ICoqtopInput>
    // io$: Rx.Observable<ICoqtopOutput<ICoqtopInput, any>>
    // error$: Rx.Observable<ValueFail>
    answer$s: {
        completed$   : Completed$
        coqExn$      : CoqExn$
        stmAdded$    : Added$
        stmCanceled$ : Canceled$
    }
    feedback$s: {
        message$s: {
            debug$   : Debug$
            error$   : Error$
            info$    : Info$
            notice$  : Notice$
            warning$ : Warning$
        },
        //   addedAxiom$: Rx.Observable<IFeedback<FeedbackContent.IAddedAxiom>>
        //   fileDependency$: Rx.Observable<IFeedback<FeedbackContent.IFileDependency>>
        //   fileLoaded$: Rx.Observable<IFeedback<FeedbackContent.IFileLoaded>>
        processed$: Processed$
        //   processingIn$: Rx.Observable<IFeedback<FeedbackContent.IProcessingIn>>
    }
    // feedback$: Rx.Observable<IFeedback<IFeedbackContent>>
    // // response$: Rx.Observable<ICoqtopResponse<ICoqtopInput, any>>
    // message$: Rx.Observable<IMessage>
    // // stateId$: Rx.Observable<number>
    // valueFail$: Rx.Observable<IValueFail>
    // // Only contains responses from ValueGood
    // valueGood$s: {
    //   add$: Rx.Observable<ICoqtopOutput<CoqtopInput.IAddPrime, CoqtopOutput.AddPrime>>
    //   editAt$: Rx.Observable<ICoqtopOutput<CoqtopInput.IEditAt, CoqtopOutput.EditAt>>
    // }
}
