abstract class PrimToken { }

class Numeral extends PrimToken {
  constructor(public numeral: number) { super() }
}

class PrimTokenString extends PrimToken {
  constructor(public str: string) { super() }
}
