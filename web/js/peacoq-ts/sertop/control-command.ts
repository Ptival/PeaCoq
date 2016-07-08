export type ControlCommand = StmAdd | StmEditAt | StmState | Quit

interface AddOptions {
  limit?: number;
  ontop?: StateId;
  newtip?: StateId;
  verb?: boolean;
}

function boolToSexp(b: boolean): string {
  return b ? "True" : "False";
}

function optionalToSexp<T>(name, option: T | undefined, printer?: (t: T) => string): string {
  return option === undefined ? "" : `(${name} ${printer ? printer(option) : option})`;
}

export class LibAdd implements ISertop.IControlCommand {
  constructor(
    public qualifiedPath: string[],
    public physicalPath: string,
    public containsML: boolean
  ) { }
  toSexp() {
    const qPath = `"${this.qualifiedPath.join(`" "`)}"`;
    return `(LibAdd (${qPath}) "${this.physicalPath}" ${boolToSexp(this.containsML)})`;
  }
}

export class StmAdd implements ISertop.IControlCommand {
  constructor(
    public addOptions: AddOptions,
    public sentence: string
  ) { }
  toSexp() {
    const opts = "".concat(
      optionalToSexp("limit", this.addOptions.limit),
      optionalToSexp("ontop", this.addOptions.ontop),
      optionalToSexp("newtip", this.addOptions.newtip),
      optionalToSexp("verb", this.addOptions.verb, b => b ? "True" : "False")
    );
    const o1 = optionalToSexp("limit", this.addOptions.limit);
    return `(StmAdd (${opts}) "${this.sentence}")`
  }
}

export class StmCancel implements ISertop.IControlCommand {
  constructor(
    public stateIds: StateId[]
  ) { }
  toSexp() {
    const ids = this.stateIds.join(" ");
    return `(StmCancel (${ids}))`;
  }
}

export class StmEditAt implements ISertop.IControlCommand {
  constructor(
    public stateId: StateId
  ) { }
  toSexp() { return `(StmEditAt ${this.stateId})`; }
}

// export class StmJoin implements Sertop.IControlCommand {
//   toSexp() { return "StmJoin"; }
// }

export class StmObserve implements ISertop.IControlCommand {
  constructor(
    public stateId: StateId
  ) { }
  toSexp() { return `(StmObserve ${this.stateId})`; }
}

export class StmQuery implements ISertop.IControlCommand {
  constructor(
    public stateId: StateId,
    public query: string
  ) { }
  toSexp() { return `(StmQuery ${this.stateId} "${this.query}"`; }
}

export class StmState implements ISertop.IControlCommand {
  toSexp() { return "StmState"; }
}

export class Quit implements ISertop.IControlCommand {
  toSexp() { return "Quit"; }
}
