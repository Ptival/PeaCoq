export default PpCut;

export abstract class PpCut { }

export class PpBrk extends PpCut {
  n1: number; n2: number;
  constructor(a: number, b: number) { super(); this.n1 = a; this.n2 = b; }
}

export class PpTbrk extends PpCut {
  n1: number; n2: number;
  constructor(a: number, b: number) { super(); this.n1 = a; this.n2 = b; }
}

export class PpTab extends PpCut { }

export class PpFnl extends PpCut { }
