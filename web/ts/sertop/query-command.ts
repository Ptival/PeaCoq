
export class Goals implements ISertop.IQueryCommand.IGoals {
  constructor(
    public stateId: StateId
  ) { }
  public toSexp() {
    return `(Goals ${this.stateId})`
  }
}
