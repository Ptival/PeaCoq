import * as _ from 'lodash'

import * as CaseStyle from '../case-style'
import * as EvarKinds from './evar-kinds'
import * as MiscTypes from './misctypes'
import * as PpExtend from '../interp/ppextend'
import { C_AST } from '../lib/c-ast'
import * as GenArg from '../lib/genarg'
import { Located } from '../lib/loc'
import * as LibNames from '../library/libnames'

export type ConstrExprR
    = CRef
    | CFix
    | CCoFix
    | CProdN
    | CLambdaN
    | CLetIn
    | CAppExpl
    | CApp
// | CRecord
    | CCases
    | CLetTuple
// | CIf
    | CHole
// | CPatVar
// | CEvar
    | CSort
// | CCast
    | CNotation
// | CGeneralization
    | CPrim
    | CDelimiters

export type ConstrExpr = C_AST<ConstrExprR>

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

export class CApp {
    constructor(
        public funct : AppFun,
        public args : AppArgs
    ) { }
}

type AppExplFun = [ProjFlag, LibNames.Reference, Maybe<InstanceExpr>]
export class CAppExpl {
    constructor(
        public readonly funct : AppExplFun,
        public readonly args : ConstrExpr[]
    ) { }
}

type CaseExpr = [
    ConstrExpr,
    Maybe<MiscTypes.lname>,
    Maybe<CasesPatternExpr>
]

export type BranchExpr = C_AST<[
    CasesPatternExpr[][],
    ConstrExpr
]>

export class CCases {
    constructor(
        public caseStyle : CaseStyle.CaseStyle,
        public returnType : Maybe<ConstrExpr>,
        public cases : CaseExpr[],
        public branches : BranchExpr[]
    ) { }
}

export class CCoFix {
    private tag : 'CCoFix'
    // TODO
}

export class CDelimiters {
    constructor(
        public str : string,
        public expr : ConstrExpr
    ) { }
}

export class CFix {
    private tag : 'CFix'
    constructor(
    ) { }
}

export class CHole {
    constructor(
        public evarKinds : Maybe<EvarKinds.T>,
        public introPatternNamingExpr : MiscTypes.IntroPatternNamingExpr,
        public rawGenericArgument : Maybe<GenArg.RawGenericArgument>,
    ) { }
}

export class CLambdaN {
    constructor(
        public binders : LocalBinderExpr[],
        public body : ConstrExpr
    ) { }
}

export class CLetIn {
    constructor(
        public name : MiscTypes.lname,
        public bound : ConstrExpr,
        public type : Maybe<ConstrExpr>,
        public body : ConstrExpr,
    ) { }
}

export class CLetTuple {
    constructor(
        public names : MiscTypes.lname[],
        public returnType : [Maybe<MiscTypes.lname>, Maybe<ConstrExpr>],
        public bound : ConstrExpr,
        public body : ConstrExpr
    ) { }
}

export type Notation = String

export class CNotation {
    constructor(
        public notation : Notation,
        public substitution : ConstrNotationSubstitution,
        public precedence : number,
        public unparsing : PpExtend.Unparsing[]
    ) { }
}

export class CProdN {
    constructor(
        public binderList : LocalBinderExpr[],
        public returnExpr : ConstrExpr
    ) { }
}

export class CPrim {
    constructor(
        public token : PrimToken
    ) { }
}

export class CRef {
    constructor(
        public reference : LibNames.Reference,
        public universeInstance : Maybe<InstanceExpr>
    ) { }
}

export class CSort {
    constructor(
        public globSort : GlobSort
    ) { }
}

export type LocalBinderExpr
    = CLocalAssum
    | CLocalDef
    | CLocalPattern

export class CLocalAssum {
    constructor(
        public readonly names : MiscTypes.lname[],
        public readonly binderKind : BinderKind,
        public readonly type : ConstrExpr,
    ) { }
}

export class CLocalDef {
    constructor(
        public readonly name : MiscTypes.lname,
        public readonly value : ConstrExpr,
        public readonly optionalType : Maybe<ConstrExpr>,
    ) { }
}

export class CLocalPattern {
    constructor(
        public readonly pattern : C_AST<[CasesPatternExpr, Maybe<ConstrExpr>]>,
    ) { }
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

export type CasesPatternExpr = C_AST<CasesPatternExprR>

export type CasesPatternExprR
    = CPatCstr
    | CPatAtom
    | CPatNotation
    | CPatPrim
    | CPatDelimiters

// TODO CPatAlias

export class CPatCstr {
    constructor(
        public reference : LibNames.Reference,
        public cases1 : Maybe<CasesPatternExpr[]>,
        public cases2 : CasesPatternExpr[]
    ) { }
}

export class CPatAtom {
    constructor(
        public reference : Maybe<LibNames.Reference>
    ) { }
}

// TODO CPatAtom
// TODO CPatOr

type CasesPatternNotationSubstitution = [
    CasesPatternExpr[],
    CasesPatternExpr[][]
]

export class CPatNotation {
    constructor(
        public notation : Notation,
        public substitution : CasesPatternNotationSubstitution,
        public patterns : CasesPatternExpr[],
        // the next fields are added by PeaCoq to simplify things
        public precedence : number,
        public unparsing : PpExtend.Unparsing[]
    ) { }
}
// TODO CPatNotation

export class CPatPrim {
    constructor(
        public token : PrimToken
    ) { }
}

// TODO CPatRecord

export class CPatDelimiters {
    constructor(
        public str : string,
        public cases : CasesPatternExpr
    ) { }
}
