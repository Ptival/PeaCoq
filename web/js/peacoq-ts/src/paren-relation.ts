export default ParenRelation;

export abstract class ParenRelation { }

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

type PrecAssoc = [number, ParenRelation];

let lAtom = 0;
let lProd = 200;
let lLambda = 200;
let lIf = 200;
let lLetIn = 200;
let lLetPattern = 200;
let lFix = 200;
let lCast = 100;
let lArg = 9;
let lApp = 10;
let lPosInt = 0;
let lNegInt = 35;
let lTop: PrecAssoc = [200, new E()];
let lProj = 1;
let lDelim = 1;
let lSimpleConstr: PrecAssoc = [8, new E()];
let lSimplePatt: PrecAssoc = [1, new E()];

export function precLess(child: number, parent: PrecAssoc) {
  let [parentPrec, parentAssoc] = parent;
  if (parentPrec < 0 && child === lProd) {
    return true;
  }
  parentPrec = Math.abs(parentPrec);
  if (parentAssoc instanceof E) { return child <= parentPrec; }
  if (parentAssoc instanceof L) { return child < parentPrec; }
  if (parentAssoc instanceof Prec) { return child <= parentAssoc.precedence; }
  if (parentAssoc instanceof Any) { return true; }
}
