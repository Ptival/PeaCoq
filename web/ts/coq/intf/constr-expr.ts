import * as _ from 'lodash'

import * as EvarKinds from './evar-kinds'
import * as MiscTypes from './misctypes'
import { cAST } from '../lib/c-ast'
import * as GenArg from '../lib/genarg'
import * as PpExtend from '../interp/ppextend'

export abstract class ConstrExprR { }

export type ConstrExpr = cAST<ConstrExprR>

export type ConstrNotationSubstitution = [
    ConstrExpr[],
    ConstrExpr[][],
    CasesPatternExpr[],
    LocalBinderExpr[][]
]

type ProjFlag = Maybe<number>

type AppFun = [ProjFlag, ConstrExpr]
export type AppArg = [ConstrExpr, Maybe<Located<Explicitation>>]
export type AppArgs = AppArg[]

export class CApp extends ConstrExprR {
    constructor(
        public funct : AppFun,
        public args : AppArgs
    ) {
        super()
    }
}

type CaseExpr = [
    ConstrExpr,
    Maybe<MiscTypes.lname>,
    Maybe<CasesPatternExpr>
]

export type BranchExpr = cAST<[
    CasesPatternExpr[][],
    ConstrExpr
]>

export class CCases extends ConstrExprR {
    constructor(
        public caseStyle : CaseStyle,
        public returnType : Maybe<ConstrExpr>,
        public cases : CaseExpr[],
        public branches : BranchExpr[]
    ) {
        super()
    }
}

export class CCoFix extends ConstrExprR {
    // TODO
}

export class CDelimiters extends ConstrExprR {
    constructor(
        public str : string,
        public expr : ConstrExpr
    ) {
        super()
    }
}

export class CFix extends ConstrExprR {
    constructor(
    ) { super() }
}

export class CHole extends ConstrExprR {
    constructor(
        public evarKinds : Maybe<EvarKinds.t>,
        public introPatternNamingExpr : MiscTypes.IntroPatternNamingExpr,
        public rawGenericArgument : Maybe<GenArg.RawGenericArgument>,
    ) {
        super()
    }
}

export class CLambdaN extends ConstrExprR {
    constructor(
        public binders : LocalBinderExpr[],
        public body : ConstrExpr
    ) {
        super()
    }
}

export class CLetIn extends ConstrExprR {
    constructor(
        public name : MiscTypes.lname,
        public bound : ConstrExpr,
        public type : Maybe<ConstrExpr>,
        public body : ConstrExpr,
    ) {
        super()
    }
}

export class CLetTuple extends ConstrExprR {
    constructor(
        public names : MiscTypes.lname[],
        public returnType : [Maybe<MiscTypes.lname>, Maybe<ConstrExpr>],
        public bound : ConstrExpr,
        public body : ConstrExpr
    ) {
        super()
    }
}

export type Notation = String

export class CNotation extends ConstrExprR {
    constructor(
        public notation : Notation,
        public substitution : ConstrNotationSubstitution,
        public precedence : number,
        public unparsing : PpExtend.Unparsing[]
    ) {
        super()
    }
}

export class CProdN extends ConstrExprR {
    constructor(
        public binderList : LocalBinderExpr[],
        public returnExpr : ConstrExpr
    ) {
        super()
    }
}

export class CPrim extends ConstrExprR {
    constructor(
        public token : PrimToken
    ) {
        super()
    }
}

export class CRef extends ConstrExprR {
    constructor(
        public reference : Reference,
        public universeInstance : Maybe<InstanceExpr>
    ) {
        super()
    }
}

export class CSort extends ConstrExprR {
    constructor(
        public globSort : GlobSort
    ) {
        super()
    }
}

export abstract class LocalBinderExpr { }

export class CLocalAssum extends LocalBinderExpr {
    constructor(
        public readonly names : MiscTypes.lname[],
        public readonly binderKind : BinderKind,
        public readonly type : ConstrExpr,
    ) { super() }
}

export class CLocalDef extends LocalBinderExpr {
    constructor(
        public readonly name : MiscTypes.lname,
        public readonly value : ConstrExpr,
        public readonly optionalType : Maybe<ConstrExpr>,
    ) { super() }
}

export class CLocalPattern extends LocalBinderExpr {
    constructor(
        public readonly pattern : cAST<[CasesPatternExpr, Maybe<ConstrExpr>]>,
    ) { super() }
}

// added for PeaCoq
// export function extractProdBinders(a : ConstrExprR) : [LocalBinderExpr[], ConstrExprR] {
//     if (a instanceof CProdN) {
//         const [bl, c] : [any[], any] = [a.binderList, a.returnExpr]
//         if (bl.length === 0) {
//             return extractProdBinders(a.returnExpr)
//         } else {
//             const [nal, bk, t] = bl[0]
//             const [blrec, cRest] = extractProdBinders(new CProdN(_.tail(bl), c))
//             const l : LocalBinderExpr[] = [new CLocalAssum(nal, bk, t)]
//             return [l.concat(blrec), cRest]
//         }
//     }
//     return [[], a]
// }

// added for PeaCoq, much less useful than in the past now
// export function extractLamBinders(a : ConstrExprR) : [LocalBinderExpr[], ConstrExprR] {
//     if (a instanceof CLambdaN) {
//         const [lamBinders, rest] = extractLamBinders(a.body)
//         return [
//             ([] as LocalBinderExpr[]).concat(a.binders, lamBinders),
//             rest
//         ]
//     } else {
//         return [[], a]
//     }
// }

export type CasesPatternExpr = cAST<CasesPatternExprR>

export abstract class CasesPatternExprR {}

// TODO CPatAlias

export class CPatCstr extends CasesPatternExprR {
    constructor(
        public reference : Reference,
        public cases1 : Maybe<CasesPatternExpr[]>,
        public cases2 : CasesPatternExpr[]
    ) {
        super()
    }
}

export class CPatAtom extends CasesPatternExprR {
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

export class CPatNotation extends CasesPatternExprR {
    constructor(
        public notation : Notation,
        public substitution : CasesPatternNotationSubstitution,
        public patterns : CasesPatternExpr[],
        // the next fields are added by PeaCoq to simplify things
        public precedence : number,
        public unparsing : PpExtend.Unparsing[]
    ) {
        super()
    }
}
// TODO CPatNotation

export class CPatPrim extends CasesPatternExprR {
    constructor(
        public token : PrimToken
    ) {
        super()
    }
}

// TODO CPatRecord

export class CPatDelimiters extends CasesPatternExprR {
    constructor(
        public str : string,
        public cases : CasesPatternExpr
    ) {
        super()
    }
}
