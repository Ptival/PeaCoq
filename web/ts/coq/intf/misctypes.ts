import { cAST } from '../lib/c-ast'
import * as Names from '../kernel/names'

export type lname = cAST<Name>

export abstract class IntroPatternNamingExpr {}
export class IntroIdentifier extends IntroPatternNamingExpr { constructor(public readonly id : Names.Id.t) { super() } }
export class IntroFresh      extends IntroPatternNamingExpr { constructor(public readonly id : Names.Id.t) { super() } }
export class IntroAnonymous  extends IntroPatternNamingExpr { constructor()                                { super() } }
