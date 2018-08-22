export class Status {
  public statusPath : string[]
  public statusProofName : string
  public statusAllProofs : string
  public statusProofNum : number
  constructor(status : [string[], string, string, number]) {
    this.statusPath = status[0]
    this.statusProofName = status[1]
    this.statusAllProofs = status[2]
    this.statusProofNum = status[3]
  }
}
