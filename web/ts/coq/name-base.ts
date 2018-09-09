abstract class NameBase { }

class Name extends NameBase {
  constructor(public id : string) { super() }
}

class Anonymous extends NameBase {
    private tag : 'Anonymous'
}
