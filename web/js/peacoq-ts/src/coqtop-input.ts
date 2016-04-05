export abstract class CoqtopInput {
  // the user might want to attach data that gets copied in the output
  data: any;
  abstract getArgs(): Object;
  abstract getCmd(): string;
}

export class AddPrime extends CoqtopInput {
  add: string;
  constructor(a: string) {
    super();
    this.add = a;
  }
  getArgs() { return this.add; }
  getCmd() { return "add'"; }
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

export class Goal extends CoqtopInput {
  constructor() { super(); }
  getArgs() { return []; }
  getCmd() { return "goal"; }
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

export class QueryPrime extends CoqtopInput {
  query: string;
  constructor(s: string) {
    super();
    this.query = s;
  }
  getArgs() { return this.query; }
  getCmd() { return "query'"; }
}
