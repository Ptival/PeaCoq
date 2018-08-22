abstract class Explicitation {}

class ExplByPos extends Explicitation {
  constructor(
    public num : number,
    public name : Maybe<string>
  ) {
    super()
  }
}

class ExplByName extends Explicitation {
  constructor(
    public name : string
  ) {
    super()
  }
}
