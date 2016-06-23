export type ControlCommand = StmAdd | StmEditAt | StmState | Quit

export class StmAdd implements Sertop.IControlCommand {
  constructor(
    public limit: number,
    public stateId: Maybe<number>,
    public sentence: string
  ) { }
  toSexp() {
    const stateId = this.stateId.caseOf({
      nothing: () => "None",
      just: (sid) => `(Just ${sid})`,
    });
    return `(StmAdd ${this.limit} ${stateId} "${this.sentence}")`
  }
}

export class StmEditAt implements Sertop.IControlCommand {
  constructor(
    public stateId: number
  ) { }
  toSexp() { return `(StmEditAt ${this.stateId})`; }
}

export class StmJoin implements Sertop.IControlCommand {
  toSexp() { return "StmJoin"; }
}

export class StmState implements Sertop.IControlCommand {
  toSexp() { return "StmState"; }
}

export class Quit implements Sertop.IControlCommand {
  toSexp() { return "Quit"; }
}
