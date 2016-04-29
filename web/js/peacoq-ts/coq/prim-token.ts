abstract class PrimToken { }

class Numeral extends PrimToken {
  constructor(public numeral: number) { super(); }
}

class PrimTokenString extends PrimToken {
  constructor(public string: string) { super(); }
}
