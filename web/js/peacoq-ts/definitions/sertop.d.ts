declare namespace Sertop {
  interface ICmd {
    tag: string;
    toSexp(): string;
  }

  interface IControlCommand {
    toSexp(): string;
  }

  interface IAnswer<K extends IAnswerKind> {
    cmdTag: string;
    answer: K;
  }

  interface IAnswerKind { }
  interface IAck extends IAnswerKind { }
  interface ICompleted extends IAnswerKind { }
  interface ICoqExn extends IAnswerKind {
    name: string;
    message: string;
  }
  interface IStmAdded extends IAnswerKind {
    stateId: StateId;
    location: CoqLocation;
    tip: INewTip | IUnfocus;
  }
  interface IStmCanceled extends IAnswerKind { }
  interface IStmCurId extends IAnswerKind { }
  interface IStmEdited extends IAnswerKind { }
}
