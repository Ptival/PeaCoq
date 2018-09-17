import * as _ from 'lodash'
import { Maybe } from 'tsmonad'

import * as PpUtils from './pputils'
import * as Option from '../clib/option'
import * as PpExtend from '../interp/ppextend'
import * as ConstrExpr from '../intf/constr-expr'
import * as MiscTypes from '../intf/misctypes'
import * as Names from '../kernel/names'
import { cAST } from '../lib/c-ast'
import * as Loc from '../lib/loc'
import * as Pp from '../lib/pp'
import * as StrToken from '../str-token'
import { PpCmdGlue } from '../lib/pp';
import * as LibNames from '../library/libnames'
import * as ParenRelation from '../paren-relation'
import * as CaseStyle from '../case-style'
import { peaCoqBox } from '../../peacoq/coq-utils'
import { MatchFailure } from '../../peacoq/utils'
import * as PeaCoqUtils from '../../peacoq/utils'
import { CasesPatternExpr, ConstrNotationSubstitution } from '../intf/constr-expr';

export type PrecAssoc = [number, ParenRelation.ParenRelation]

const lAtom = 0
const lProd = 200
const lLambda = 200
const lIf = 200
const lLetIn = 200
const lLetPattern = 200
const lFix = 200
const lCast = 100
const lArg = 9
const lApp = 10
const lPosInt = 0
const lNegInt = 35
const lTop : PrecAssoc = [200, new ParenRelation.E()]
const lProj = 1
const lDelim = 1
const lSimpleConstr : PrecAssoc = [8, new ParenRelation.E()]
const lSimplePatt : PrecAssoc = [1, new ParenRelation.E()]

export function precLess(child : number, parent : PrecAssoc) {
    const [parentPrec, parentAssoc] = parent
    if (parentPrec < 0 && child === lProd) {
        return true
    }
    const absParentPrec = Math.abs(parentPrec)
    if (parentAssoc instanceof ParenRelation.E) { return child <= absParentPrec }
    if (parentAssoc instanceof ParenRelation.L) { return child < absParentPrec }
    if (parentAssoc instanceof ParenRelation.Prec) { return child <= parentAssoc.precedence }
    if (parentAssoc instanceof ParenRelation.Any) { return true }
}

function prComAt(n : number) : Pp.T { return Pp.mt() }

function prId(id : string) : Pp.T { return Names.Id.print(id) }

function prLIdent(i : cAST<string>) : Pp.T {
    const id = i.v
    return i.loc.caseOf({
        nothing : () => prId(id),
        just : (loc : Loc.t) => {
            const [b, ] = Loc.unLoc(loc)
            return PpUtils.prLocated(prId, [Maybe.just(Loc.makeLoc(b, b + Names.Id.toString(id).length)), id])
        },
    })
}

function prName(n : Names.Name.T) : Pp.T { return Names.Name.print(n) }

function prLName(ln : MiscTypes.lname) : Pp.T {
    const v = ln.v
    if (v instanceof Name) {
        return peaCoqBox(prLIdent(new cAST(v.id, ln.loc)))
    } else {
        return peaCoqBox(PpUtils.prAST(Names.Name.print, ln))
    }
}

function surroundImpl(k : BindingKind, p : Pp.T) : Pp.T {
    if (k instanceof Explicit) { return Pp.concat(Pp.str('('), p, Pp.str(')')) }
    if (k instanceof Implicit) { return Pp.concat(Pp.str('{'), p, Pp.str('}')) }
    debugger
    throw MatchFailure('surroundImpl', k)
}

function surroundImplicit(k : BindingKind, p : Pp.T) : Pp.T {
    if (k instanceof Explicit) { return p }
    if (k instanceof Implicit) { return Pp.concat(Pp.str('{'), p, Pp.str('}')) }
    debugger
    throw MatchFailure('surroundImplicit', k)
}

function prBinder(
    many : boolean,
    pr : (c : ConstrExpr.ConstrExpr) => Pp.T,
    [nal, k, t] : [cAST<Name>[], BinderKind, ConstrExpr.ConstrExpr]
) : Pp.T {
    if (k instanceof Generalized) {
        const [b, bp, tp] = [k.kind1, k.kind2, k.b]
        debugger
        throw 'TODO : prBinder Generalized'
    }
    if (k instanceof Default) {
        const b = k.kind
        if (t instanceof ConstrExpr.CHole && t.introPatternNamingExpr instanceof MiscTypes.IntroAnonymous) {
            debugger
            throw 'TODO : prBinder CHole'
        } else {
            const s = Pp.concat(
                Pp.prListWithSep(Pp.spc, prLName, nal),
                Pp.str(' : '),
                pr(t)
            )
            return peaCoqBox(many ? surroundImpl(b, s) : surroundImplicit(b, s))
        }
    }
    debugger
    throw MatchFailure('prBinder', k)
}

function prDelimitedBinders(
    kw : (n : number) => Pp.T,
    sep : () => Pp.T,
    prC : (t : ConstrExpr.ConstrExpr) => Pp.T,
    bl : ConstrExpr.LocalBinderExpr[]
) : Pp.T {
    const n = beginOfBinders(bl)
    if (bl.length === 0) {
        debugger
        throw 'prDelimitedBinders : bl should not be empty'
    }
    const bl0 = bl[0]
    if (bl0 instanceof ConstrExpr.CLocalAssum && bl.length === 1) {
        const [nal, k, t] = [bl0.names, bl0.binderKind, bl0.type]
        return Pp.concat(kw(n), prBinder(false, prC, [nal, k, t]))
    } else {
        return Pp.concat(kw(n), prUndelimitedBinders(sep, prC, bl))
    }
}

function tagEvar(p : Pp.T) : Pp.T { return Pp.tag('evar', p) }
function tagKeyword(p : Pp.T) : Pp.T { return Pp.tag('keyword', p) }
function tagNotation(r : Pp.T) : Pp.T { return Pp.tag('notation', r) }
function tagPath(p : Pp.T) : Pp.T { return Pp.tag('path', p) }
function tagRef(r : Pp.T) : Pp.T { return Pp.tag('reference', r) }
function tagType(r : Pp.T) : Pp.T { return Pp.tag('univ', r) }
function tagVariable(p : Pp.T) : Pp.T { return Pp.tag('variable', p) }

function keyword(s : string) : Pp.T { return tagKeyword(Pp.str(s)) }

function prForall() : Pp.T {
    return Pp.concat(keyword('forall'), Pp.spc())
}

function prFun() : Pp.T {
    return Pp.concat(keyword('fun'), Pp.spc())
}

const maxInt = 9007199254740991

function prBinderAmongMany(
    prC : (t : ConstrExpr.ConstrExpr) => Pp.T,
    b : ConstrExpr.LocalBinderExpr
) : Pp.T {
    if (b instanceof ConstrExpr.CLocalAssum) {
        const [nal, k, t] = [b.names, b.binderKind, b.type]
        return prBinder(true, prC, [nal, k, t])
    }
    if (b instanceof ConstrExpr.CLocalDef) {
        const [na, c, topt] = [b.name, b.value, b.optionalType]
        // const cp, topt

        /* TODO :
           if (c instanceof CCast) {
           debugger
           throw 'TODO : prBinderAmongMany then'
           } else {
           debugger
           throw 'TODO : prBinderAmongMany else'
           }
        */

        debugger
        throw b
    }
    debugger
    throw b
}

function prUndelimitedBinders(
    sep : () => Pp.T,
    prC : (t : ConstrExpr.ConstrExpr) => Pp.T,
    l : ConstrExpr.LocalBinderExpr[]
) {
    return Pp.prListWithSep(sep, (b) => prBinderAmongMany(prC, b), l)
}

function prBindersGen(
    prC : (t : ConstrExpr.ConstrExpr) => Pp.T,
    sep : () => Pp.T,
    isOpen : boolean,
    ul : ConstrExpr.LocalBinderExpr[]
) {
    if (isOpen) {
        return prDelimitedBinders(Pp.mt, sep, prC, ul)
    } else {
        return prUndelimitedBinders(sep, prC, ul)
    }
}

function tagUnparsing(unp : PpExtend.Unparsing, pp1 : Pp.T) : Pp.T {
    if (unp instanceof PpExtend.UnpTerminal) {
        return tagNotation(pp1)
    }
    return pp1
}

function printHunks<T>(
    n : number,
    pr : (_1 : [number, ParenRelation.ParenRelation], _2 : T) => Pp.T,
    prPatt : (_1 : [number, ParenRelation.ParenRelation], _2 : ConstrExpr.CasesPatternExpr) => Pp.T,
    prBinders : (_1 : () => Pp.T, _2 : boolean, _3 : ConstrExpr.LocalBinderExpr[]) => Pp.T,
    [terms, termlists, binders, binderlists] : [T[], T[][], ConstrExpr.CasesPatternExpr[], ConstrExpr.LocalBinderExpr[][]],
    unps : PpExtend.Unparsing[]
) : Pp.T {
    const env     = terms.slice(0)
    const envlist = termlists.slice(0)
    const bl      = binders.slice(0)
    const bll     = binderlists.slice(0)
    function pop<T>(a : T[]) : T {
        const res = a.shift()
        if (res === undefined) {
            debugger
            throw a
        }
        return res
    }
    function ret(unp : PpExtend.Unparsing, pp1 : Pp.T, pp2 : Pp.T) : Pp.T {
        return Pp.concat(tagUnparsing(unp, pp1), pp2)
    }
    function aux(ul : ReadonlyArray<PpExtend.Unparsing>) : Pp.T {
        if (ul.length === 0) {
            return Pp.mt()
        }
        const unp = ul[0]
        const l = _.tail(ul)
        if (unp instanceof PpExtend.UnpMetaVar) {
            const prec = unp.parenRelation
            const c = pop(env)
            const pp2 = aux(l)
            const pp1 = pr([n, prec], c)
            return ret(unp, pp1, pp2)
        }
        if (unp instanceof PpExtend.UnpBinderMetaVar) {
            const [prec] = [unp.parenRelation]
            const c = pop(bl)
            const pp2 = aux(l)
            const pp1 = prPatt([n, prec], c)
            return ret(unp, pp1, pp2)
        }
        if (unp instanceof PpExtend.UnpListMetaVar) {
            const [prec, sl] = [unp.parenRelation, unp.unparsing]
            const cl = pop(envlist)
            const pp1 = Pp.prListWithSep(
                () => aux(sl),
                x => pr([n, prec], x),
                cl
            )
            const pp2 = aux(l)
            return ret(unp, pp1, pp2)
        }
        if (unp instanceof PpExtend.UnpBinderListMetaVar) {
            const [isOpen, sl] = [unp.isOpen, unp.unparsing]
            const cl = pop(bll)
            const pp2 = aux(l)
            const pp1 = prBinders(() => aux(sl), isOpen, cl)
            return ret(unp, pp1, pp2)
        }
        if (unp instanceof PpExtend.UnpTerminal) {
            const s = unp.terminal
            const pp2 = aux(l)
            const pp1 = Pp.str(s)
            return ret(unp, pp1, pp2)
        }
        if (unp instanceof PpExtend.UnpBox) {
            const [b, sub] = [unp.box, unp.unparsing]
            const pp1 = PpExtend.PpCmdOfBox(b, aux(sub.map(PeaCoqUtils.snd)))
            const pp2 = aux(l)
            return ret(unp, pp1, pp2)
        }
        if (unp instanceof PpExtend.UnpCut) {
            const pp2 = aux(l)
            const pp1 = PpExtend.PpCmdOfCut(unp.cut)
            return ret(unp, pp1, pp2)
        }
        throw MatchFailure('printHunks', unp)
    }
    return aux(unps)
}

type PpResult = [Pp.T, number]

// Here Coq would consult the notation table to figure [unpl] and [level] from
// [s], but we have it already figured out.
function prNotation<T>(
    pr : (_1 : [number, ParenRelation.ParenRelation], _2 : T) => Pp.T,
    prPatt : (_1 : [number, ParenRelation.ParenRelation], _2 : ConstrExpr.CasesPatternExpr) => Pp.T,
    prBinders : (_1 : () => Pp.T, _2 : boolean, _3 : ConstrExpr.LocalBinderExpr[]) => Pp.T,
    s : ConstrExpr.Notation, // ignored
    env : [T[], T[][], ConstrExpr.CasesPatternExpr[], ConstrExpr.LocalBinderExpr[][]],
    // these extra arguments are PeaCoq-specific
    unpl : PpExtend.Unparsing[],
    level : number
) : PpResult {
    return [
        printHunks(level, pr, prPatt, prBinders, env, unpl),
        level
    ]
}

function prList<T>(pr : (t : T) => Pp.T, l : T[]) : Pp.T {
    return new Pp.PpCmdGlue(l.map(pr))
}

function prGlobSortInstance<T>(i : IGlobSortGen<T>) : Pp.T {
    if (i instanceof MiscTypes.GProp) { return tagType(Pp.str('Prop')) }
    if (i instanceof MiscTypes.GSet) { return tagType(Pp.str('Set')) }
    if (i instanceof MiscTypes.GType) {
        // TODO : this is weird, it's not a Maybe, probably a bug here
        return i.type.caseOf({
            nothing : () => tagType(Pp.str('Type')),
            just : (t : string) => Pp.str(t),
        })
    }
    throw MatchFailure('prGlobSortInstance', i)
}

function prOptNoSpc<T>(pr : (t : T) => Pp.T, mx : Maybe<T>) : Pp.T {
    return mx.caseOf({
        nothing : () => Pp.mt(),
        just : x => pr(x),
    })
}

function prUnivAnnot<T>(pr : (t : T) => Pp.T, x : T) : Pp.T {
    return Pp.concat(Pp.str('@{'), pr(x), Pp.str('}'))
}

function prUniverseInstance(us : Maybe<InstanceExpr>) : Pp.T {
    return prOptNoSpc(
        x => {
            return prUnivAnnot(
                y => Pp.prListWithSep(Pp.spc, prGlobSortInstance, y),
                x
            )
        },
        us
    )
}

function prCRef(r : LibNames.Reference, us : Maybe<InstanceExpr>) : Pp.T {
    return Pp.concat(LibNames.prReference(r), prUniverseInstance(us))
}

function chop<T>(i : number, l : T[]) : [T[], T[]] {
    return [l.slice(0, i), l.slice(i)]
}

function sepLast<T>(l : T[]) : [T, T[]] {
    const len = l.length
    return [l[len - 1], l.slice(0, len - 1)]
}

function prProj(
    pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
    prApp : (
        pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
        a : ConstrExpr.ConstrExpr,
        l : ConstrExpr.AppArgs
    ) => Pp.T,
    a : ConstrExpr.ConstrExpr,
    f : ConstrExpr.ConstrExpr,
    l : ConstrExpr.AppArgs
) : Pp.T {
    return Pp.hov(
        0,
        Pp.concat(
            pr([lProj, new ParenRelation.E()], a),
            Pp.cut(),
            Pp.str('.('),
            prApp(pr, f, l),
            Pp.str(')')
        )
    )
}

function prExplArgs(
    pr : (pa : PrecAssoc, ce : ConstrExpr.ConstrExpr) => Pp.T,
    [a, mexpl] : ConstrExpr.AppArg
) : Pp.T {
    return mexpl.caseOf({
        nothing : () => pr([lApp, new ParenRelation.L()], a),
        just : expl => {
            const e = expl.some[1]
            if (e instanceof ExplByPos) {
                throw 'Anomaly : Explicitation by position not implemented'
            }
            if (e instanceof ExplByName) {
                return Pp.concat(Pp.str('('), prId(e.name), Pp.str(' :='), pr(lTop, a), Pp.str(')'))
            }
            throw MatchFailure('prExplArgs', e)
        },
    })
}

function prApp(
    pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
    a : ConstrExpr.ConstrExpr,
    l : ConstrExpr.AppArgs
) {
    return Pp.hov(
        2,
        Pp.concat(
            pr([lApp, new ParenRelation.L()], a),
            prList(a => Pp.concat(Pp.spc(), prExplArgs(pr, a)), l)
        )
    )
}

function precOfPrimToken(t : PrimToken) : number {
    if (t instanceof Numeral) {
        return t.sign ? lPosInt : lNegInt
    }
    if (t instanceof PrimTokenString) {
        return lAtom
    }
    throw MatchFailure('precOfPrimToken', t)
}

function qs(s : string) : Pp.T { return Pp.str('\'' + s + '\'') }

function prPrimToken(t : PrimToken) : Pp.T {
    if (t instanceof Numeral) {
        return Pp.str(t.sign ? t.raw : `-${t.raw}`)
    }
    if (t instanceof PrimTokenString) {
        return qs(t.str)
    }
    throw MatchFailure('prPrimToken', t)
}

function prUniv(l : string[]) {
    if (l.length === 1) {
        return Pp.str(l[0])
    } else {
        return Pp.concat(
            Pp.str('max('),
            Pp.prListWithSep(() => Pp.str(','), Pp.str, l),
            Pp.str(')')
        )
    }
}

function prGlobSort(s : GlobSort) : Pp.T {
    if (s instanceof MiscTypes.GProp) {
        return tagType(Pp.str('Prop'))
    }
    if (s instanceof MiscTypes.GSet) {
        return tagType(Pp.str('Set'))
    }
    if (s instanceof MiscTypes.GType) {
        if (s.type.length === 0) {
            return tagType(Pp.str('Type'))
        } else {
            return Pp.hov(
                0,
                Pp.concat(tagType(Pp.str('Type')), prUnivAnnot(prUniv, s.type))
            )
        }
    }
    throw MatchFailure('prGlobSort', s)
}

function prDelimiters(key : string, strm : Pp.T) : Pp.T {
    return peaCoqBox(Pp.concat(strm, Pp.str('%' + key)))
}

function tagConstrExpr(ce : ConstrExpr.ConstrExpr, cmds : Pp.T) {
    return peaCoqBox(cmds)
}

function prDanglingWithFor(
    sep : () => Pp.T,
    pr : (_1 : () => Pp.T, _2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) => Pp.T,
    inherited : PrecAssoc,
    a : ConstrExpr.ConstrExpr
) : Pp.T {
    if (a.v instanceof ConstrExpr.CFix || a.v instanceof ConstrExpr.CCoFix) {
        throw 'TODO: CFix or CCoFix'
    }
    return pr(sep, inherited, a)
}

function prWithComments(
    loc : Maybe<Loc.t>,
    pp : Pp.T
) : Pp.T {
    return PpUtils.prLocated(x => x, [loc, pp])
}

function prPatt(
    sep : () => Pp.T,
    inh : PrecAssoc,
    p : ConstrExpr.CasesPatternExpr
) : Pp.T {

    function match(pp : ConstrExpr.CasesPatternExprR) : [Pp.T, number] {
        // TODO ConstrExpr.CPatRecord
        // TODO ConstrExpr.CPatAlias
        if (pp instanceof ConstrExpr.CPatCstr) {
            return pp.cases1.caseOf<[Pp.T, number]>({
                nothing : () => {
                    if (pp.cases2.length === 0) {
                        return [LibNames.prReference(pp.reference), lAtom]
                    } else {
                        return [
                            Pp.concat(
                                LibNames.prReference(pp.reference),
                                prList(
                                    (x : ConstrExpr.CasesPatternExpr) => prPatt(Pp.spc, [lApp, new ParenRelation.L()], x),
                                    pp.cases2
                                )
                            ),
                            lApp
                        ]
                    }
                },
                just : cases1 => {
                    if (pp.cases2.length === 0) {
                        return [
                            Pp.concat(
                                Pp.str('@'),
                                LibNames.prReference(pp.reference),
                                prList(
                                    x => prPatt(Pp.spc, [lApp, new ParenRelation.L()], x),
                                    cases1
                                )
                            ),
                            lApp
                        ]
                    }
                    return [
                        Pp.concat(
                            Pp.surround(Pp.concat(
                                Pp.str('@'),
                                LibNames.prReference(pp.reference),
                                prList(
                                    x => prPatt(Pp.spc, [lApp, new ParenRelation.L()], x),
                                    cases1
                                )
                            )),
                            prList(
                                x => prPatt(Pp.spc, [lApp, new ParenRelation.L()], x),
                                pp.cases2
                            )
                        ),
                        lApp
                    ]
                },
            })
        } else if (pp instanceof ConstrExpr.CPatAtom) {
            const r = pp.reference
            return r.caseOf<PpResult>({
                nothing : () => [Pp.str('_'), lAtom],
                just : r => [LibNames.prReference(r), lAtom],
            })
            // } else if (p instanceof ConstrExpr.CPatOr) {
            // TODO
        } else if (pp instanceof ConstrExpr.CPatNotation) {
            if (
                pp.notation === '( _ )'
                    && pp.substitution[0].length === 1
                    && pp.substitution[1].length === 0
                    && pp.patterns.length === 0
            ) {
                const p = pp.substitution[0][0]
                return [
                    Pp.concat(
                        prPatt(() => Pp.str('('), [Number.MAX_VALUE, new ParenRelation.E()], p),
                        Pp.str(')')
                    )
                    , lAtom
                ]
            } else {
                const s = pp.notation
                const [l, ll] = pp.substitution
                const args = pp.patterns
                const [strmNot, lNot] = prNotation(
                    (x, y) => prPatt(Pp.mt, x, y),
                    (x : any, y : any) => Pp.mt(),
                    (x : any, y : any, z : any) => Pp.mt(),
                    s,
                    [[], [], [], []],
                    pp.unparsing,
                    pp.precedence
                )
                const prefix =
                    (args.length === 0 || precLess(lNot, [lApp, new ParenRelation.L()]))
                    ? strmNot
                    : Pp.surround(strmNot)
                return [
                    Pp.concat(prefix, prList(x => prPatt(Pp.spc, [lApp, new ParenRelation.L()], x), args)),
                    args.length === 0 ? lNot : lApp
                ]
            }
        } else if (pp instanceof ConstrExpr.CPatPrim) {
            return [prPrimToken(pp.token), lAtom]
        } else if (pp instanceof ConstrExpr.CPatDelimiters) {
            return [
                prDelimiters(pp.str, prPatt(Pp.mt, lSimplePatt, pp.cases)),
                1
            ]
        } else {
            throw MatchFailure('prPatt > match', pp)
        }
    }

    const [strm, prec] = match(p.v)
    const loc = p.loc
    return prWithComments(loc, Pp.concat(
        sep(),
        precLess(prec, inh) ? strm : Pp.surround(strm)
    ))
}

function prAsin(
    pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
    mna : Maybe<MiscTypes.lname>,
    indnalopt : Maybe<ConstrExpr.CasesPatternExpr>
) : Pp.T {
    return Pp.concat(
        mna.caseOf({
            nothing : () => Pp.mt(),
            just : na => Pp.concat(
                Pp.spc(),
                keyword('as'),
                Pp.spc(),
                prLName(na)
            ),
        }),
        indnalopt.caseOf({
            nothing : () => Pp.mt(),
            just : i => Pp.concat(
                Pp.spc(),
                keyword('in'),
                Pp.spc(),
                prPatt(Pp.mt, lSimplePatt, i)
            ),
        })
    )
}

function prCaseItem(
    pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
    [tm, asClause, inClause] : [ConstrExpr.ConstrExpr, Maybe<cAST<Name>>, Maybe<ConstrExpr.CasesPatternExpr>]
) : Pp.T {
    return Pp.hov(0, Pp.concat(
        pr([lCast, new ParenRelation.E()], tm),
        prAsin(pr, asClause, inClause)
    ))
}

function sepV() : Pp.T { return Pp.concat(Pp.str(','), Pp.spc()) }

function constrLoc(c : ConstrExpr.ConstrExpr) : Maybe<Loc.t> {
    return c.loc
}

function prSepCom(
    sep : () => Pp.T,
    f : (c : ConstrExpr.ConstrExpr) => Pp.T,
    c : ConstrExpr.ConstrExpr
) : Pp.T {
    return prWithComments(constrLoc(c), Pp.concat(sep(), f(c)))
}

function prCaseType(
    pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
    mpo : Maybe<ConstrExpr.ConstrExpr>
) : Pp.T {
    // TODO : po instanceof CHole with IntroAnonymous
    return mpo.caseOf({
        nothing : () => Pp.mt(),
        just : po => Pp.concat(
            Pp.spc(),
            Pp.hov(2, Pp.concat(
                keyword('return'),
                prSepCom(Pp.spc, x => pr(lSimpleConstr, x), po)
            ))
        ),
    })
}

function prEqn(
    pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
    { loc, v } : ConstrExpr.BranchExpr
) : Pp.T {
    const [pl, rhs] = v
    // const pl1 = _(pl0).map((located : Located<Array<CasesPatternExpr>>) => located[1]).value()
    return Pp.concat(
        Pp.spc(),
        Pp.hov(4,
               prWithComments(
                   loc,
                   Pp.concat(
                       Pp.str('| '),
                       Pp.hov(0, Pp.concat(
                           Pp.prListWithSep(
                               Pp.prSpaceBar,
                               (x : ConstrExpr.CasesPatternExpr[]) => Pp.prListWithSep(sepV, (y : ConstrExpr.CasesPatternExpr) => prPatt(Pp.mt, lTop, y), x),
                               pl
                           ),
                           Pp.str(' =>')
                       )),
                       prSepCom(Pp.spc, x => pr(lTop, x), rhs)
                   )
               )
              )
    )
}

function prSimpleReturnType(
    pr : (_1 : PrecAssoc, _2 : ConstrExpr.ConstrExpr) => Pp.T,
    na : Maybe<MiscTypes.lname>,
    po : Maybe<ConstrExpr.ConstrExpr>
) : Pp.T {
    return (
        Pp.concat(
            na.caseOf({
                nothing : () => Pp.mt(),
                just : x => x.v instanceof Name
                    ? Pp.concat(Pp.spc(), keyword('as'), prId(x.v.id))
                    : Pp.mt()
            })
        )
    )
}

const prFunSep : Pp.T = Pp.concat(Pp.spc(), Pp.str('=>'))

function pr0(
    pr : (_1 : () => Pp.T, _2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) => Pp.T
) : (_1 : () => Pp.T, _2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) => Pp.T {
    return (
        sep : () => Pp.T,
        inherited : PrecAssoc,
        a : ConstrExpr.ConstrExpr
    ) => {

        function ret(cmds : Pp.T, prec : number) : PpResult {
            return [tagConstrExpr(a, cmds), prec]
        }

        const prmt = (x : [number, ParenRelation.ParenRelation], y : ConstrExpr.ConstrExpr) => pr(Pp.mt, x, y)

        function match(aa : ConstrExpr.ConstrExprR) : PpResult {

            if (aa instanceof ConstrExpr.CApp) {
                // TODO : ldots_var
                const pf = aa.funct[0]
                const f = aa.funct[1]
                return pf.caseOf<PpResult>({
                    nothing : () => {
                        const b = <ConstrExpr.CApp>aa // TS bug
                        const [f, l] = [b.funct[1], b.args]
                        return ret(prApp(prmt, f, l), lApp)
                    },
                    just : pf => {
                        const b = <ConstrExpr.CApp>aa // TS bug
                        const [i, f, l] = [pf, b.funct[1], b.args]
                        const [l1, l2] = chop(i, l)
                        const [c, rest] = sepLast(l1)
                        // TODO : assert c[1] is empty option?
                        const p = prProj(prmt, prApp, c[0], f, rest)
                        // TODO : it might be nice if we could highlight the structure
                        // nested applications, rather than having a flat n-ary one
                        if (l2.length > 0) {
                            return ret(
                                Pp.concat(
                                    p,
                                    prList(
                                        aaa => {
                                            return Pp.concat(Pp.spc(), prExplArgs(prmt, aaa))
                                        },
                                        l2
                                    )
                                ),
                                lApp
                            )
                        } else {
                            return [p, lProj]
                        }
                    },
                })
            }

            if (aa instanceof ConstrExpr.CCases) {
                if (aa.caseStyle instanceof CaseStyle.LetPatternStyle) {
                    debugger
                    throw 'TODO : LetPatternStyle'
                }
                const [rtnTypOpt, c, eqns] = [aa.returnType, aa.cases, aa.branches]
                const prDangling = (pa : [number, ParenRelation.ParenRelation], c : ConstrExpr.ConstrExpr) => prDanglingWithFor(Pp.mt, pr, pa, c)
                return ret(
                    Pp.v(0,
                         Pp.hv(0, Pp.concat(
                             keyword('match'),
                             Pp.brk(1, 2),
                             Pp.hov(0,
                                    Pp.prListWithSep(
                                        sepV,
                                        x => prCaseItem(prDangling, x),
                                        aa.cases
                                    )
                                   ),
                             prCaseType(prDangling, aa.returnType),
                             Pp.spc(),
                             keyword('with'),
                             prList(
                                 (e : ConstrExpr.BranchExpr) => prEqn((x, y) => pr(Pp.mt, x, y), e),
                                 aa.branches
                             ),
                             Pp.spc(),
                             keyword('end')
                         ))),
                    lAtom
                )
            }

            if (aa instanceof ConstrExpr.CDelimiters) {
                const [sc, e] = [aa.str, aa.expr]
                return ret(
                    prDelimiters(sc, pr(Pp.mt, [lDelim, new ParenRelation.E()], e)),
                    lDelim
                )
            }

            if (aa instanceof ConstrExpr.CLambdaN) {
                const [bl, a] = [aa.binders, aa.body]
                return ret(
                    Pp.hov(0, Pp.concat(
                        Pp.hov(2, prDelimitedBinders(prFun, Pp.spc, x => pr(Pp.mt, lTop, x), bl)),
                        prFunSep,
                        pr(Pp.spc, lTop, a)
                    )),
                    lLambda
                )
            }

            if (aa instanceof ConstrExpr.CLetIn) {
                const [x, a, t, b] = [aa.name, aa.bound, aa.type, aa.body]
                if (a instanceof ConstrExpr.CFix || a instanceof ConstrExpr.CCoFix) {
                    debugger
                    throw ('TODO : pr CLetIn with CFix/CcoFix')
                }
                return ret(
                    Pp.hv(0, Pp.concat(
                        Pp.hov(2, Pp.concat(
                            keyword('let'), Pp.spc(), prLName(x),
                            prOptNoSpc(t => Pp.concat(Pp.str(' :'), Pp.ws(1), pr(Pp.mt, lTop, t)), t),
                            Pp.str(' :='), pr(Pp.spc, lTop, a), Pp.spc(), keyword('in')
                        )),
                        pr(Pp.spc, lTop, aa.body)
                    )),
                    lLetIn
                )
            }

            if (aa instanceof ConstrExpr.CLetTuple) {
                const [nal, [na, po], c, b] = [aa.names, aa.returnType, aa.bound, aa.body]
                return ret(
                    Pp.hv(0,
                          Pp.hov(2,
                                 Pp.concat(
                                     keyword('let'),
                                     Pp.spc(),
                                     Pp.hov(1, Pp.concat(
                                         Pp.str('('),
                                         Pp.prListWithSep(sepV, prLName, nal),
                                         Pp.str(')'),
                                         prSimpleReturnType(prmt, na, po),
                                         Pp.str(' :='),
                                         pr(Pp.spc, lTop, aa.bound),
                                         Pp.spc(),
                                         keyword('in')
                                     )),
                                     pr(Pp.spc, lTop, aa.body)
                                 )
                                )
                         ),
                    lLetIn
                )
            }

            if (aa instanceof ConstrExpr.CNotation) {
                if (aa.notation === '(\u00A0_\u00A0)') {
                    const [[t], [], []] = aa.substitution
                    return ret(
                        Pp.concat(
                            pr(
                                () => { return Pp.str('(') },
                                [maxInt, new ParenRelation.L()],
                                t
                            ),
                            Pp.str(')')
                        ),
                        lAtom
                    )
                } else {
                    const [s, env] = [aa.notation, aa.substitution]
                    return prNotation(
                        (x : [number, ParenRelation.ParenRelation], y : ConstrExpr.ConstrExpr) => pr(Pp.mt, x, y),
                        (x, y) => prPatt(Pp.mt, x, y),
                        (x : () => Pp.T, y : boolean, z : ConstrExpr.LocalBinderExpr[]) => prBindersGen(w => pr(Pp.mt, lTop, w), x, y, z),
                        s,
                        env,
                        aa.unparsing,
                        aa.precedence
                    )
                }
            }

            if (aa instanceof ConstrExpr.CPrim) {
                return ret(
                    prPrimToken(aa.token),
                    precOfPrimToken(aa.token)
                )
            }

            if (aa instanceof ConstrExpr.CProdN) {
                const [bl, a] = [aa.binderList, aa.returnExpr]
                return ret(
                    Pp.concat(
                        prDelimitedBinders(
                            prForall,
                            Pp.spc,
                            x => pr(Pp.mt, lTop, x),
                            bl
                        ),
                        Pp.str(','),
                        pr(Pp.spc, lTop, a)
                    ),
                    lProd
                )
            }

            if (aa instanceof ConstrExpr.CRef) {
                const [r, us] = [aa.reference, aa.universeInstance]
                return ret(
                    prCRef(r, us),
                    lAtom
                )
            }

            if (aa instanceof ConstrExpr.CSort) {
                return ret(prGlobSort(aa.globSort), lAtom)
            }

            debugger
            throw MatchFailure('pr > match', aa)

        }

        const [strm, prec] = match(a.v)

        return (
            Pp.concat(
                sep(),
                precLess(prec, inherited)
                    ? strm
                    : Pp.surround(strm)
            )
        )

    }
}

function pr1(_2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) : Pp.T {
    const pr : (_1 : () => Pp.T, _2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) => Pp.T = PeaCoqUtils.fix(pr0)
    return pr(Pp.mt, _2, _3)
}

function pr2(_2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) : Pp.T {
    if (_3.v instanceof ConstrExpr.CAppExpl) {
        const [ [pf, f, us], args ] = [ _3.v.funct , _3.v.args ]
        if (PeaCoqUtils.isNothing(pf) && args.length === 0) {
            return Pp.concat(Pp.str("@"), prCRef(f, us))
        }
    }
    return pr1(_2, _3)
}

function prExpr(prec : PrecAssoc, c : ConstrExpr.ConstrExpr) {
    // FIXME: ignoring `transf` for now
    return pr2(prec, c)
}

function prConstrExprN(n : PrecAssoc, c : ConstrExpr.ConstrExpr) {
    return prExpr(n, c)
}

function prSimpleConstr(x : ConstrExpr.ConstrExpr) { return prExpr(lSimpleConstr, x) }

const defaultTermPr = {
    prConstrExpr         : prSimpleConstr,
    prLConstrExpr        : (x : ConstrExpr.ConstrExpr) => prExpr(lTop, x),
    prConstrPatternExpr  : prSimpleConstr,
    prLConstrPatternExpr : (x : ConstrExpr.ConstrExpr) => prExpr(lTop, x),
}

export function prConstrExpr(c : ConstrExpr.ConstrExpr) : Pp.T {
    return defaultTermPr.prConstrExpr(c)
}

function prLConstrExpr(c : ConstrExpr.ConstrExpr) : Pp.T {
    return defaultTermPr.prLConstrExpr(c)
}

function prConstrPatternExpr(c : ConstrExpr.ConstrExpr) : Pp.T {
    return defaultTermPr.prConstrPatternExpr(c)
}

function prLConstrPatternExpr(c : ConstrExpr.ConstrExpr) : Pp.T {
    return defaultTermPr.prLConstrPatternExpr(c)
}

function prHTMLGen(
    pr : (_1 : () => Pp.T, _2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) => Pp.T
) : (_1 : () => Pp.T, _2 : PrecAssoc, _3 : ConstrExpr.ConstrExpr) => Pp.T {
    const recur = pr0(pr)
    return (sep : () => Pp.T, pa : PrecAssoc, e : ConstrExpr.ConstrExpr) => {
        return Pp.concat(
            Pp.str(`<span class='ace_editor syntax'>`),
            recur(sep, pa, e),
            Pp.str('</span>')
        )
    }
}

function prHTML(a : ConstrExpr.ConstrExpr) : Pp.T {
    return PeaCoqUtils.fix(prHTMLGen)(Pp.mt, lTop, a)
}

function dumbPrintPpCmd(p : Pp.T) : string {
    if (p instanceof Pp.PpCmdBox) {
        // FIXME : use blockType
        return dumbPrintPpCmds(p.contents)
    }
    if (p instanceof Pp.PpCmdPrintBreak) {
        return ' '.repeat(p.nspaces)
    }
    if (p instanceof Pp.PpCmdForceNewline) {
        return 'TODO : PpExtend.PpCmdForceNewline'
    }
    if (p instanceof Pp.PpCmdComment) {
        return 'TODO : PpExtend.PpCmdComment'
    }
    debugger
    throw MatchFailure('dumbPrintPpCmd', p)
}

function dumbPrintStrToken(t : StrToken.StrToken) : string {
    if (t instanceof StrToken.StrDef) {
        return t.str
    }
    if (t instanceof StrToken.StrLen) {
        return t.str
    }
    debugger
    throw MatchFailure('dumbPrintStrToken', t)
}

function dumbPrintPpCmds(l : Pp.T) : string {
    return _.reduce(
        l,
        (acc, p) => { return acc + dumbPrintPpCmd(p) },
        ''
    )
}

function beginOfBinder(lBi : ConstrExpr.LocalBinderExpr) : number {
    const bLoc = (l : Maybe<Loc.t>) => (Option.cata(Loc.unLoc, [0, 0], l))[0]
    if (lBi instanceof ConstrExpr.CLocalDef)     { return bLoc(lBi.name.loc) }
    if (lBi instanceof ConstrExpr.CLocalAssum)   { return bLoc(lBi.names[0].loc) }
    if (lBi instanceof ConstrExpr.CLocalPattern) { return bLoc(lBi.pattern.loc) }
    debugger
    throw MatchFailure('beginOfBinder', lBi)
}

function beginOfBinders(bl : ConstrExpr.LocalBinderExpr[]) {
    if (bl.length === 0) { return 0 }
    else { return beginOfBinder(bl[0]) }
}
