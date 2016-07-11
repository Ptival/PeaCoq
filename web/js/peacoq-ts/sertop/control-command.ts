import * as Sexp from "./sexp";

interface AddOptions {
  limit?: number;
  ontop?: StateId;
  newtip?: StateId;
  verb?: boolean;
}

export class LibAdd implements ISertop.IControlCommand {
  constructor(
    public qualifiedPath: string[],
    public physicalPath: string,
    public containsML: boolean
  ) { }
  toSexp() {
    const qPath = `"${this.qualifiedPath.join(`" "`)}"`;
    return `(LibAdd (${qPath}) "${this.physicalPath}" ${Sexp.boolToSexp(this.containsML)})`;
  }
}

export class StmAdd implements ISertop.IControlCommand {
  constructor(
    public addOptions: AddOptions,
    public sentence: string
  ) { }
  toSexp() {
    const opts = "".concat(
      Sexp.optionalToSexp("limit", this.addOptions.limit),
      Sexp.optionalToSexp("ontop", this.addOptions.ontop),
      Sexp.optionalToSexp("newtip", this.addOptions.newtip),
      Sexp.optionalToSexp("verb", this.addOptions.verb, b => b ? "True" : "False")
    );
    const o1 = Sexp.optionalToSexp("limit", this.addOptions.limit);
    return `(StmAdd (${opts}) "${this.sentence.replace(/\"/g, `\\"`)}")`
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
  toSexp() { return `(StmQuery ${this.stateId} "${this.query}")`; }
}

export class StmState implements ISertop.IControlCommand {
  toSexp() { return "StmState"; }
}

export class Quit implements ISertop.IControlCommand {
  toSexp() { return "Quit"; }
}
