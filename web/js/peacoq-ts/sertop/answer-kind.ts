import * as Exception from "./exception";
import * as Tip from "../coq/tip";
import * as SertopUtils from "./utils";

export class Ack implements ISertop.IAck { }

export class Completed implements ISertop.ICompleted { }

export class CoqExn implements ISertop.ICoqExn {
  constructor(
    public exn: IException
  ) { }
  getMessage(): string { return this.exn.getMessage(); }
}

export class StmAdded implements ISertop.IStmAdded {
  constructor(
    public stateId: StateId,
    public location: CoqLocation,
    public tip: Tip.NewTip | Tip.Unfocus
  ) { }
}

export class StmCanceled implements ISertop.IStmCanceled {
  constructor(
    public stateIds: number[]
  ) { }
}

export class StmCurId implements ISertop.IStmCurId {
  constructor(
    public curId: number
  ) { }
}

export class StmEdited implements ISertop.IStmEdited {
  constructor(
    public tip: Tip.NewTip // | Focus
  ) { }
}

export function create(o): ISertop.IAnswerKind {
  if (typeof o === "string") {
    switch (o) {
      case "Ack": return new Ack();
      case "Completed": return new Completed();
      default: debugger;
    }
  }
  const [kind, ...args] = o;
  switch (kind) {

    case "CoqExn":
      const [[kind, ...payload]] = args;
      return new CoqExn(Exception.create(kind, payload));

    case "StmAdded": { // opening a scope prevents hoisted variable clashes
      const [stateId, coqLocation, tip]: [string, string, string] = args;
      return new StmAdded(+ stateId, SertopUtils.coqLocationFromSexp(coqLocation), tip);
    }

    case "StmCurId":
      const [curId] = args;
      return new StmCurId(curId);

    case "StmEdited":
      const [tip] = args;
      if (tip === "NewTip") {
        return new StmEdited(new Tip.NewTip());
      } else {
        debugger;
      }

    case "StmCanceled":
      const [stateIds] = args;
      return new StmCanceled(stateIds);

    default: debugger;
  }

  throw "AnswerKind.create";
}
