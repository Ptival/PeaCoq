/*
DO NOT TURN THIS FILE INTO A MODULE UNLESS YOU CHANGE THE HASKELL
CODE TO RETURN QUALIFIED EXPRESSIONS!
*/

abstract class ConstrExpr { }

type BinderExpr = [
  Array<Located<NameBase>>,
  BinderKind,
  ConstrExpr
];

type ConstrNotationSubstitution = [
  Array<ConstrExpr>,
  Array<Array<ConstrExpr>>,
  Array<Array<LocalBinder>>
];

type ProjFlag = Maybe<number>;

type AppFun = [ProjFlag, ConstrExpr];
type AppArg = [ConstrExpr, Maybe<Located<Explicitation>>];
type AppArgs = AppArg[];

class CApp extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public funct: AppFun,
    public args: AppArgs
  ) {
    super();
  }
}

type CaseExpr = [
  ConstrExpr,
  [Maybe<Located<Name>>, Maybe<CasesPatternExpr>]
];

type BranchExpr = [
  CoqLocation,
  Array<Located<Array<CasesPatternExpr>>>,
  ConstrExpr
];

class CCases extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public caseStyle: CaseStyle,
    public returnType: Maybe<ConstrExpr>,
    public cases: CaseExpr[],
    public branches: BranchExpr[]
  ) {
    super();
  }
}

class CCoFix extends ConstrExpr {
  // TODO
}

class CDelimiters extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public string: string,
    public expr: ConstrExpr
  ) {
    super();
  }
}

class CFix extends ConstrExpr {
  // TODO
}

class CHole extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public evarKinds,
    public introPatternNamingExpr,
    public rawGenericArgument
  ) {
    super();
  }
}

class CLambdaN extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public binders: Array<BinderExpr>,
    public body: ConstrExpr
  ) {
    super();
  }
}

class CLetIn extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public name: Located<Name>,
    public bound: ConstrExpr,
    public body: ConstrExpr
  ) {
    super();
  }
}

class CLetTuple extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public names: Array<Located<Name>>,
    public returnType: [Maybe<Located<Name>>, Maybe<ConstrExpr>],
    public bound: ConstrExpr,
    public body: ConstrExpr
  ) {
    super();
  }
}

type Notation = String;

class CNotation extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public notation: Notation,
    public substitution: ConstrNotationSubstitution,
    public precedence: number,
    public unparsing: Array<Unparsing>
  ) {
    super();
  }
}

class CProdN extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public binderList: Array<BinderExpr>,
    public returnExpr: ConstrExpr
  ) {
    super();
  }
}

class CPrim extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public token: PrimToken
  ) {
    super();
  }
}

class CRef extends ConstrExpr {
  constructor(
    public reference: Reference,
    public universeInstance: Maybe<InstanceExpr>
  ) {
    super();
  }
}

class CSort extends ConstrExpr {
  constructor(
    public location: CoqLocation,
    public globSort: GlobSort
  ) {
    super();
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
