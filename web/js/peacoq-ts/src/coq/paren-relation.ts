export default ParenRelation;

export abstract class ParenRelation { }

export class E extends ParenRelation { }

export class L extends ParenRelation { }

export class Prec extends ParenRelation {
  precedence: number;
  constructor(prec: number) {
    super();
    this.precedence = prec;
  }
}

export class Any extends ParenRelation { }
