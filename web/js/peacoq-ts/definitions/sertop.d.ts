declare namespace ISertop {
  interface ICmd {
    tag: number;
    toSexp(): string;
  }

  interface IControlCommand {
    toSexp(): string;
  }

  interface IStmCancel extends IControlCommand {
    
  }

  interface IStmQuery extends IControlCommand {
    stateId: StateId;
  }

  interface IAnswer<K extends IAnswerKind> {
    cmdTag: string;
    answer: K;
  }

  interface IAnswerKind { }
  interface IAck extends IAnswerKind { }
  interface ICompleted extends IAnswerKind { }
  interface ICoqExn extends IAnswerKind {
    exn: IException;
    getMessage(): string;
  }
  interface IStmAdded extends IAnswerKind {
    stateId: StateId;
    location: CoqLocation;
    tip: INewTip | IUnfocus;
  }
  interface IStmCanceled extends IAnswerKind {
    stateIds: number[];
  }
  interface IStmCurId extends IAnswerKind { }
  interface IStmEdited extends IAnswerKind { }
}

interface IException {
  getMessage(): string;
}
