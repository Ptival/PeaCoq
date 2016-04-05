abstract class ParenRelation { }

class E extends ParenRelation { }

class L extends ParenRelation { }

class Prec extends ParenRelation {
  precedence: number;
  constructor(prec: number) {
    super();
    this.precedence = prec;
  }
}

class Any extends ParenRelation { }
