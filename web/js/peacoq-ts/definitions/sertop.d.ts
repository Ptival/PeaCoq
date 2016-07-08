interface ToSexp {
  toSexp(): string;
}

declare namespace ISertop {

  interface ICommand extends ToSexp {
    tag: number;
  }

  interface IControl extends ICommand { }
  interface IQuery extends ICommand { }

  interface IControlCommand extends ToSexp { }
  interface IQueryCommand extends ToSexp { }

  namespace IControlCommand {
    interface IStmCancel extends IControlCommand { }
    interface IStmQuery extends IControlCommand {
      stateId: StateId;
    }
  }

  namespace IQueryCommand {
    interface IGoals extends IQueryCommand { }
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
