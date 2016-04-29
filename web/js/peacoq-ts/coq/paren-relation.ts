abstract class ParenRelation { }

class E extends ParenRelation { }

class L extends ParenRelation { }

class Prec extends ParenRelation {
  constructor(
    public precedence: number
  ) {
    super();
  }
}

class Any extends ParenRelation { }
