
export class AddPrime implements CoqtopInput.IAddPrime {
  constructor(
    public add: string
  ) { }
  getArgs() { return this.add; }
  getCmd() { return "add'"; }
}

export class EditAt implements CoqtopInput.IEditAt {
  constructor(
    public stateId: number
  ) { }
  getArgs() { return this.stateId; }
  getCmd() { return `(Control (StmEditAt ${this.stateId}))`; }
}

export class Goal implements CoqtopInput.IGoal {
  getArgs() { return []; }
  getCmd() { return "goal"; }
}

export class Status implements CoqtopInput.IStatus {
  constructor(
    public b: boolean
  ) { }
  getArgs() { return this.b; }
  getCmd() { return "status"; }
}

export class Query implements CoqtopInput.IQuery {
  constructor(
    public query: string,
    public stateId: number
  ) { }
  getArgs() { return [this.query, this.stateId]; }
  getCmd() { return "query"; }
}

export class QueryPrime implements CoqtopInput.IQueryPrime {
  constructor(
    public query: string
  ) { }
  getArgs() { return this.query; }
  getCmd() { return "query'"; }
}
