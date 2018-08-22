// import PrimToken from "./prim-token"
// import Reference from "./reference"

abstract class CasesPatternExpr { }

// TODO CPatAlias

class CPatCstr extends CasesPatternExpr {
  constructor(
    public location : CoqLocation,
    public reference : Reference,
    public cases1 : Maybe<CasesPatternExpr[]>,
    public cases2 : CasesPatternExpr[]
  ) {
    super()
  }
}

class CPatAtom extends CasesPatternExpr {
  constructor(
    public location : CoqLocation,
    public reference : Maybe<Reference>
  ) {
    super()
  }
}

// TODO CPatAtom
// TODO CPatOr

type CasesPatternNotationSubstitution = [
  CasesPatternExpr[],
  CasesPatternExpr[][]
]

class CPatNotation extends CasesPatternExpr {
  constructor(
    public location : CoqLocation,
    public notation : Notation,
    public substitution : CasesPatternNotationSubstitution,
    public patterns : CasesPatternExpr[],
    public precedence : number,
    public unparsing : Unparsing[]
  ) {
    super()
  }
}
// TODO CPatNotation

class CPatPrim extends CasesPatternExpr {
  constructor(
    public location : CoqLocation,
    public token : PrimToken
  ) {
    super()
  }
}

// TODO CPatRecord

class CPatDelimiters extends CasesPatternExpr {
  constructor(
    public location : CoqLocation,
    public str : string,
    public cases : CasesPatternExpr
  ) {
    super()
  }
}
