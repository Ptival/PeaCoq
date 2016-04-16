/*
DO NOT TURN THIS FILE INTO A MODULE UNLESS YOU CHANGE THE HASKELL
CODE TO RETURN QUALIFIED EXPRESSIONS!
*/

abstract class ConstrExpr {}

type BinderExpr =[
  Array<Located<NameBase>>,
  BinderKind,
  ConstrExpr
];

type ConstrNotationSubstitution =[
  Array<ConstrExpr>,
  Array<Array<ConstrExpr>>,
  Array<Array<LocalBinder>>
];

type ProjFlag = Maybe<number>;

type AppFun =[ProjFlag, ConstrExpr];
type AppArg =[ConstrExpr, Maybe<Located<Explicitation>>];
type AppArgs = AppArg[];

class CApp extends ConstrExpr {
  location: CoqLocation;
  function: AppFun;
  arguments: AppArgs;
  constructor(loc: CoqLocation, f, args) {
    super();
    this.location = loc;
    this.function = f;
    this.arguments = args;
  }
}

type CaseExpr =[
  ConstrExpr,
  [Maybe<Located<Name>>, Maybe<CasesPatternExpr>]
];

type BranchExpr =[
  CoqLocation,
  Array<Located<Array<CasesPatternExpr>>>,
  ConstrExpr
];

class CCases extends ConstrExpr {
  location: CoqLocation;
  caseStyle: CaseStyle;
  returnType: Maybe<ConstrExpr>;
  cases: CaseExpr[];
  branches: BranchExpr[];
  constructor(loc, style, ceo, casel, branchl) {
    super();
    this.location = loc;
    this.caseStyle = style;
    this.returnType = ceo;
    this.cases = casel;
    this.branches = branchl;
  }
}

class CCoFix extends ConstrExpr {
  // TODO
}

class CDelimiters extends ConstrExpr {
  location: CoqLocation;
  string: string;
  expr: ConstrExpr;
  constructor(l, s, e) {
    super();
    this.location = l;
    this.string = s;
    this.expr = e;
  }
}

class CFix extends ConstrExpr {
  // TODO
}

class CHole extends ConstrExpr {
  location: CoqLocation;
  // evarKinds
  // introPatternNamingExpr
  // rawGenericArgument
  constructor(loc: CoqLocation, eko, ipne, rgao) {
    super();
    this.location = loc;
  }
}

class CLambdaN extends ConstrExpr {
  location: CoqLocation;
  binders: Array<BinderExpr>;
  body: ConstrExpr;
  constructor(loc: CoqLocation, bel: Array<BinderExpr>, ce: ConstrExpr) {
    super();
    this.location = loc;
    this.binders = bel;
    this.body = ce;
  }
}

class CLetIn extends ConstrExpr {
  location: CoqLocation;
  name: Located<Name>;
  bound: ConstrExpr;
  body: ConstrExpr;
  constructor(loc: CoqLocation, n, ce1, ce2) {
    super();
    this.location = loc;
    this.name = n;
    this.bound = ce1;
    this.body = ce2;
  }
}

class CLetTuple extends ConstrExpr {
  location: CoqLocation;
  names: Array<Located<Name>>;
  returnType: [Maybe<Located<Name>>, Maybe<ConstrExpr>];
  bound: ConstrExpr;
  body: ConstrExpr;
  constructor(l, nll, p, ce1, ce2) {
    super();
    this.location = l;
    this.names = nll;
    this.returnType = p;
    this.bound = ce1;
    this.body = ce2;
  }
}

type Notation = String;

class CNotation extends ConstrExpr {
  location: CoqLocation;
  notation: Notation;
  substitution: ConstrNotationSubstitution;
  precedence: number;
  unparsing: Array<Unparsing>;
  constructor(
    l: CoqLocation, n: Notation, cns: ConstrNotationSubstitution,
    prec: number, unpl: Array<Unparsing>
    ) {
    super();
    this.location = l;
    this.notation = n;
    this.substitution = cns;
    this.precedence = prec;
    this.unparsing = unpl;
  }
}

class CProdN extends ConstrExpr {
  location: CoqLocation;
  binderList: Array<BinderExpr>;
  returnExpr: ConstrExpr;
  constructor(l: CoqLocation, bel: Array<BinderExpr>, ce: ConstrExpr) {
    super();
    this.location = l;
    this.binderList = bel;
    this.returnExpr = ce;
  }
}

class CPrim extends ConstrExpr {
  location: CoqLocation;
  token: PrimToken;
  constructor(l: CoqLocation, pt: PrimToken) {
    super();
    this.location = l;
    this.token = pt;
  }
}

class CRef extends ConstrExpr {
  ref: Reference;
  universeInstance: Maybe<InstanceExpr>;
  constructor(r: Reference, i: Maybe<InstanceExpr>) {
    super();
    this.ref = r;
    this.universeInstance = i;
  }
}

class CSort extends ConstrExpr {
  location: CoqLocation;
  globSort: GlobSort;
  constructor(l: CoqLocation, gs: GlobSort) {
    super();
    this.location = l;
    this.globSort = gs;
  }
}

function extractProdBinders(a: ConstrExpr): [Array<LocalBinder>, ConstrExpr] {
  if (a instanceof CProdN) {
    let [loc, bl, c] = [a.location, a.binderList, a.returnExpr];
    if (bl.length === 0) {
      return extractProdBinders(a.returnExpr);
    } else {
      let [nal, bk, t] = bl[0];
      let [blrec, cRest] = extractProdBinders(new CProdN(loc, _.tail(bl), c));
      let l: LocalBinder[] = [new LocalRawAssum(nal, bk, t)];
      return [l.concat(blrec), cRest];
    }
  }
  return [[], a];
}
