
export class AddPrime implements ICoqtopInput {
  constructor(
    public add: string
  ) { }
  getArgs() { return this.add; }
  getCmd() { return "add'"; }
}

export class EditAt implements ICoqtopInput {
  constructor(
    public stateId: number
  ) { }
  getArgs() { return this.stateId; }
  getCmd() { return "editat"; }
}

export class Goal implements ICoqtopInput {
  getArgs() { return []; }
  getCmd() { return "goal"; }
}

export class Status implements ICoqtopInput {
  constructor(
    public b: boolean
  ) { }
  getArgs() { return this.b; }
  getCmd() { return "status"; }
}

export class Query implements ICoqtopInput {
  constructor(
    public query: string,
    public stateId: number
  ) { }
  getArgs() { return [this.query, this.stateId]; }
  getCmd() { return "query"; }
}

export class QueryPrime implements ICoqtopInput {
  constructor(
    public query: string
  ) { }
  getArgs() { return this.query; }
  getCmd() { return "query'"; }
}
