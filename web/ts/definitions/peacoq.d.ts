// input
type Command$ = Rx.Observable<ISertop.ICommand>
type ControlCommand$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand>>

type StmAdd$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmAdd>>
type StmCancel$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmCancel>>
type StmEditAt$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmEditAt>>
type StmObserve$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmObserve>>
type StmQuery$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmQuery>>

// output
type Completed$ = Rx.Observable<ISertop.IAnswer<ISertop.ICompleted>>
type CoqExn$ = Rx.Observable<ISertop.IAnswer<ISertop.ICoqExn>>

type StmAdded$ = Rx.Observable<ISertop.IAnswer<ISertop.IStmAdded>>
type StmCanceled$ = Rx.Observable<ISertop.IAnswer<ISertop.IStmCanceled>>

// feedback
type Processed$ = Rx.Observable<IFeedback<IFeedbackContent.IProcessed>>

// message feedback
type Error$ = Rx.Observable<ErrorMessageFeedback>
type Notice$ = Rx.Observable<NoticeMessageFeedback>

declare const enum PeaCoqMessageLevel {
  Default,
  Danger,
  Info,
  Success,
  Warning,
}

interface PeaCoqContextElement {
  goal: IGoal
  ppgoal: IPeaCoqGoal
}

type PeaCoqContext = IGoals<PeaCoqContextElement>

interface IPeaCoqGoal {
  hyps: PeaCoqHyp[]
  concl: IConstrExpr
  getHTML(): JQuery
}

interface PeaCoqHyp {
  name: string
  maybeTerm: Maybe<IConstrExpr>
  type: IConstrExpr
}
