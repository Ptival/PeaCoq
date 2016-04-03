export default PrimToken;

export abstract class PrimToken { }

export class Numeral extends PrimToken {
  numeral: number;
  constructor(n: number) {
    super();
    this.numeral = n;
  }
}

export class PrimTokenString extends PrimToken {
  string: string;
  constructor(s: string) {
    super();
    this.string = s;
  }
}
