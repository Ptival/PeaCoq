export abstract class CoqtopInput {
  // the user might want to attach data that gets copied in the output
  data: any;
  abstract getArgs(): Object;
  abstract getCmd(): string;
}

export class AddPrime extends CoqtopInput {
  constructor(
    public add: string
  ) {
    super();
  }
  getArgs() { return this.add; }
  getCmd() { return "add'"; }
}

export class EditAt extends CoqtopInput {
  constructor(
    public stateId: number
  ) {
    super();
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
  constructor(
    public b: boolean
  ) {
    super();
    this.b = b;
  }
  getArgs() { return this.b; }
  getCmd() { return "status"; }
}

export class QueryPrime extends CoqtopInput {
  constructor(
    public query: string
  ) {
    super();
  }
  getArgs() { return this.query; }
  getCmd() { return "query'"; }
}
