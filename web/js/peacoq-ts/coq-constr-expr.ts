type Notation = string;

class ConstrExpr { }

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

class Explicitation { }

class ExplByPos extends Explicitation {
  number: number;
  name: Maybe<string>;
  constructor(n: number, id: Maybe<string>) {
    super();
    this.number = n;
    this.name = id;
  }
}

class ExplByName extends Explicitation {
  name: string;
  constructor(id: string) {
    super();
    this.name = id;
  }
}

type AppFun =[ProjFlag, ConstrExpr];
type AppArg =[ConstrExpr, Maybe<Located<Explicitation>>];
type AppArgs = AppArg[];

class CApp extends ConstrExpr {
  location: Location;
  function: AppFun;
  arguments: AppArgs;
  constructor(loc: Location, f, args) {
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
  Location,
  Array<Located<Array<CasesPatternExpr>>>,
  ConstrExpr
];

class CCases extends ConstrExpr {
  location: Location;
  caseStyle: CaseStyle;
  constrExpr: Maybe<ConstrExpr>;
  cases: CaseExpr[];
  branches: BranchExpr[];
  constructor(loc, style, ceo, casel, branchl) {
    super();
    this.location = loc;
    this.caseStyle = style;
    this.constrExpr = ceo;
    this.cases = casel;
    this.branches = branchl;
  }
}

class CHole extends ConstrExpr {
  location: Location;
  // evarKinds
  // introPatternNamingExpr
  // rawGenericArgument
  constructor(loc: Location, eko, ipne, rgao) {
    super();
    this.location = loc;
  }
}

class CNotation extends ConstrExpr {
  location: Location;
  notation: Notation;
  substitution: ConstrNotationSubstitution;
  precedence: number;
  unparsing: Array<Unparsing>;
  constructor(
    l: Location, n: Notation, cns: ConstrNotationSubstitution,
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
  location: Location;
  binderList: Array<BinderExpr>;
  returnExpr: ConstrExpr;
  constructor(l: Location, bel: Array<BinderExpr>, ce: ConstrExpr) {
    super();
    this.location = l;
    this.binderList = bel;
    this.returnExpr = ce;
  }
}

class CPrim extends ConstrExpr {
  location: Location;
  token: PrimToken;
  constructor(l: Location, pt: PrimToken) {
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
  location: Location;
  globSort: GlobSort;
  constructor(l: Location, gs: GlobSort) {
    super();
    this.location = l;
    this.globSort = gs;
  }
}
