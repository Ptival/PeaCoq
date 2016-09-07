type Completed$ = Rx.Observable<ISertop.IAnswer<ISertop.ICompleted>>
type ControlCommand$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand>>
type CoqExn$ = Rx.Observable<ISertop.IAnswer<ISertop.ICoqExn>>
type StmAdd$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmAdd>>
type StmAdded$ = Rx.Observable<ISertop.IAnswer<ISertop.IStmAdded>>
type StmCancel$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmCancel>>
type StmCanceled$ = Rx.Observable<ISertop.IAnswer<ISertop.IStmCanceled>>
type StmEditAt$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmEditAt>>
type StmObserve$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmObserve>>
type StmQuery$ = Rx.Observable<ISertop.IControl<ISertop.IControlCommand.IStmQuery>>

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
