export default PpBox;

export abstract class PpBox { }

export class PpHB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

export class PpHoVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

export class PpHVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

export class PpVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

export class PpTB extends PpBox { }
