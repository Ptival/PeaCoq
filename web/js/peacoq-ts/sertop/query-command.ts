
export class Goals implements ISertop.IQueryCommand.IGoals {
  constructor(
    public stateId: StateId
  ) { }
  toSexp() {
    return `(Goals ${this.stateId})`;
  }
}
