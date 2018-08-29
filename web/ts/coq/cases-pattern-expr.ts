// import PrimToken from "./prim-token"
// import Reference from "./reference"

abstract class CasesPatternExprR implements ICasesPatternExprR { }

// TODO CPatAlias

class CPatCstr extends CasesPatternExprR {
    constructor(
        public reference : Reference,
        public cases1 : Maybe<CasesPatternExpr[]>,
        public cases2 : CasesPatternExpr[]
    ) {
        super()
    }
}

class CPatAtom extends CasesPatternExprR {
    constructor(
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

class CPatNotation extends CasesPatternExprR {
    constructor(
        public notation : Notation,
        public substitution : CasesPatternNotationSubstitution,
        public patterns : CasesPatternExpr[],
        // the next fields are added by PeaCoq to simplify things
        public precedence : number,
        public unparsing : Unparsing[]
    ) {
        super()
    }
}
// TODO CPatNotation

class CPatPrim extends CasesPatternExprR {
    constructor(
        public token : PrimToken
    ) {
        super()
    }
}

// TODO CPatRecord

class CPatDelimiters extends CasesPatternExprR {
    constructor(
        public str : string,
        public cases : CasesPatternExpr
    ) {
        super()
    }
}
