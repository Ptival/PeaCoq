import * as Exception from "./exception";
import * as Tip from "../coq/tip";
import * as SertopUtils from "./utils";

export class Ack implements Sertop.IAck { }

export class Completed implements Sertop.ICompleted { }

export class CoqExn implements Sertop.ICoqExn {
  constructor(
    public exn: IException
  ) { }
  getMessage(): string { return this.exn.getMessage(); }
}

export class StmAdded implements Sertop.IStmAdded {
  constructor(
    public stateId: StateId,
    public location: CoqLocation,
    public tip: Tip.NewTip | Tip.Unfocus
  ) { }
}

export class StmCanceled implements Sertop.IStmCanceled {
  constructor(
    public stateIds: number[]
  ) { }
}

export class StmCurId implements Sertop.IStmCurId {
  constructor(
    public curId: number
  ) { }
}

export class StmEdited implements Sertop.IStmEdited {
  constructor(
    public tip: Tip.NewTip // | Focus
  ) { }
}

export function create(o): Sertop.IAnswerKind {
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
      const [stateId, coqLocation, tip] = args;
      return new StmAdded(stateId, SertopUtils.coqLocationFromSexp(coqLocation), tip);
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
