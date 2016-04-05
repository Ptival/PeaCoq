abstract class PrimToken { }

class Numeral extends PrimToken {
  numeral: number;
  constructor(n: number) {
    super();
    this.numeral = n;
  }
}

class PrimTokenString extends PrimToken {
  string: string;
  constructor(s: string) {
    super();
    this.string = s;
  }
}
