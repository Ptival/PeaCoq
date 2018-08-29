type CommandTag = string
type RouteId = number

interface ToSexp {
    toSexp(): string
}

declare namespace ISertop {

    interface QueryOptions {
        // preds?: QueryPred[]
        // limit?: Maybe<number>
        sid?: StateId
        // pp?: PrintOptions
        route?: RouteId
    }

    interface ICommand extends ToSexp {
        tag: CommandTag
    }

    interface IControl<C extends IControlCommand> extends ICommand {
        controlCommand: C
    }
    interface IQuery<Q extends IQueryCommand> extends ICommand {
        queryCommand: Q
    }

    interface IControlCommand extends ToSexp { }
    interface IQueryCommand extends ToSexp { }

    namespace IControlCommand {
        interface IStmAdd extends IControlCommand {
            fromAutomation: boolean
            // addOptions: AddOptions
            sentence: string
        }
        interface IStmCancel extends IControlCommand { }
        // interface IStmEditAt extends IControlCommand { }
        interface IStmExec extends IControlCommand {
            stateId: StateId
        }
        // interface IStmObserve extends IControlCommand {
        //   stateId: StateId
        // }
        interface IStmQuery extends IControlCommand {
            fromAutomation: boolean
            query: IQueryCommand
            queryOptions: QueryOptions
        }
    }

    namespace IQueryCommand {
        interface IGoals extends IQueryCommand { }
        interface IVernac extends IQueryCommand {
            vernac : string
        }
    }

    interface IAnswer<K extends IAnswerKind> {
        cmdTag: CommandTag
        answer: K
    }

    interface IAnswerKind { }
    interface IAck extends IAnswerKind { }
    interface ICompleted extends IAnswerKind { }
    interface ICoqExn extends IAnswerKind {
        exn: IException
        getMessage(): string
    }
    interface IObjList extends IAnswerKind {
        objects : any[]
    }
    interface IStmAdded extends IAnswerKind {
        stateId: StateId
        location: CoqLocation
        tip: INewTip | IUnfocus
    }
    interface IStmCanceled extends IAnswerKind {
        stateIds: number[]
    }
    interface IStmCurId extends IAnswerKind { }
    interface IStmEdited extends IAnswerKind { }
}

interface IException {
    getMessage(): string
}

interface CoqtopOutputStreams {
    // all inputs/outputs
    // input$: Rx.Observable<ICoqtopInput>
    // io$: Rx.Observable<ICoqtopOutput<ICoqtopInput, any>>
    // error$: Rx.Observable<ValueFail>
    answer$s: {
        completed$: Completed$
        coqExn$: CoqExn$
        stmAdded$: StmAdded$
        stmCanceled$: StmCanceled$
    }
    feedback$s: {
        message$s: {
            debug$: Rx.Observable<DebugMessageFeedback>
                error$: Error$
            info$: Rx.Observable<InfoMessageFeedback>
                notice$: Notice$
            warning$: Rx.Observable<WarningMessageFeedback>
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
