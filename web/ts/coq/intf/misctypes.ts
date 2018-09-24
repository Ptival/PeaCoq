import { C_AST } from '../lib/c-ast'
import * as Names from '../kernel/names'

export type lname = C_AST<Name>

export abstract class IntroPatternNamingExpr {}
export class IntroIdentifier extends IntroPatternNamingExpr { constructor(public readonly id : Names.Id.T) { super() } }
export class IntroFresh      extends IntroPatternNamingExpr { constructor(public readonly id : Names.Id.T) { super() } }
export class IntroAnonymous  extends IntroPatternNamingExpr { constructor()                                { super() } }

export type GlobSortGen<A>
    = GProp
    | GSet
    | GType<A>

export class GProp {
    private tag : 'GProp'
}

export class GSet {
    private tag : 'GSet'
}

export class GType<T> {
    constructor(public type : T) { }
}
