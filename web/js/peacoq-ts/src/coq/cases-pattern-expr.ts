// import PrimToken from "./prim-token";
// import Reference from "./reference";

abstract class CasesPatternExpr { }

// TODO CPatAlias

class CPatCstr extends CasesPatternExpr {
  location: Location;
  reference: Reference;
  cases1: CasesPatternExpr[];
  cases2: CasesPatternExpr[];
  constructor(
    l: Location, r: Reference, c1: CasesPatternExpr[], c2: CasesPatternExpr[]
    ) {
    super();
    this.location = l;
    this.reference = r;
    this.cases1 = c1;
    this.cases2 = c2;
  }
}

class CPatAtom extends CasesPatternExpr {
  location: Location;
  reference: Maybe<Reference>;
  constructor(l: Location, r: Maybe<Reference>) {
    super();
    this.location = l;
    this.reference = r;
  }
}

// TODO CPatAtom
// TODO CPatOr
// TODO CPatNotation

class CPatPrim extends CasesPatternExpr {
  location: Location;
  token: PrimToken;
  constructor(l: Location, t: PrimToken) {
    super();
    this.location = l;
    this.token = t;
  }
}

// TODO CPatRecord

class CPatDelimiters extends CasesPatternExpr {
  location: Location;
  string: string;
  cases: CasesPatternExpr;
  constructor(l: Location, s: string, c: CasesPatternExpr) {
    super();
    this.location = l;
    this.string = s;
    this.cases = c;
  }
}
