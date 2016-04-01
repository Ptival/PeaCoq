export abstract class PpCut { }

class PpBrk extends PpCut {
  n1: number; n2: number;
  constructor(a: number, b: number) { super(); this.n1 = a; this.n2 = b; }
}

class PpTbrk extends PpCut {
  n1: number; n2: number;
  constructor(a: number, b: number) { super(); this.n1 = a; this.n2 = b; }
}

class PpTab extends PpCut { }

class PpFnl extends PpCut { }
