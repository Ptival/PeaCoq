
export class Goals implements ISertop.IQueryCommand.IGoals {
  constructor(
    public stateId: StateId
  ) { }
  public toSexp(): string {
    return `(Goals ${this.stateId})`
  }
}
