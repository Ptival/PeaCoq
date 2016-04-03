export class Status {
  statusPath: string[];
  statusProofName: string;
  statusAllProofs: string;
  statusProofNum: number;
  constructor(status) {
    this.statusPath = status[0];
    this.statusProofName = status[1];
    this.statusAllProofs = status[2];
    this.statusProofNum = status[3];
  }
}
