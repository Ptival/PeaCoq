import Edit from "./edit";

export default CoqtopInput;

export abstract class CoqtopInput {
  abstract getArgs(): Object;
  abstract getCmd(): string;
}

export class AddPrime extends CoqtopInput {
  add: string;
  edit: Maybe<Edit>;
  constructor(a: string, e: Maybe<Edit>) {
    super();
    this.add = a;
    this.edit = e;
  }
  getArgs() { return this.add; }
  getCmd() { return "add'"; }
  hasEdit(): boolean {
    return isJust(this.edit);
  }
}

export class EditAt extends CoqtopInput {
  stateId: number;
  constructor(sid: number) {
    super();
    this.stateId = sid;
  }
  getArgs() { return this.stateId; }
  getCmd() { return "editat"; }
}

export class Status extends CoqtopInput {
  b: boolean;
  constructor(b: boolean) {
    super();
    this.b = b;
  }
  getArgs() { return this.b; }
  getCmd() { return "status"; }
}
