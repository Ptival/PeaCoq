import * as _ from 'lodash'

import { PpHBox, PpVBox, PpHVBox, PpHoVBox, PpTBox } from '../coq/block-type'
import * as PpCmd from '../coq/ppcmd-token'
import * as StrToken from '../coq/str-token'

export type PpCmd = PpCmd.PpCmdToken<StrToken.StrToken>
export type PpCmds = PpCmd[]

export type PrecAssoc = [number, ParenRelation]

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
const lTop : PrecAssoc = [200, new E()]
const lProj = 1
const lDelim = 1
const lSimpleConstr : PrecAssoc = [8, new E()]
const lSimplePatt : PrecAssoc = [1, new E()]

export function precLess(child : number, parent : PrecAssoc) {
  const [parentPrec, parentAssoc] = parent
  if (parentPrec < 0 && child === lProd) {
    return true
  }
  const absParentPrec = Math.abs(parentPrec)
  if (parentAssoc instanceof E) { return child <= absParentPrec }
  if (parentAssoc instanceof L) { return child < absParentPrec }
  if (parentAssoc instanceof Prec) { return child <= parentAssoc.precedence }
  if (parentAssoc instanceof Any) { return true }
}

/*
peaCoqBox should not disrupt the pretty-printing flow, but add a
<span> so that sub-expression highlighting is more accurate
*/
function peaCoqBox(l : PpCmds) : PpCmds {
  return [new PpCmd.PpCmdBox(new PpHoVBox(0), l)]
}

export function h(n : number, s : PpCmds) : PpCmds { return [new PpCmd.PpCmdBox(new PpHBox(n), s)] }
export function v(n : number, s : PpCmds) : PpCmds { return [new PpCmd.PpCmdBox(new PpVBox(n), s)] }
export function hv(n : number, s : PpCmds) : PpCmds { return [new PpCmd.PpCmdBox(new PpHVBox(n), s)] }
export function hov(n : number, s : PpCmds) : PpCmds { return [new PpCmd.PpCmdBox(new PpHoVBox(n), s)] }
export function t(s : PpCmds) : PpCmds { return [new PpCmd.PpCmdBox(new PpTBox(), s)] }

function cut() : PpCmds { return [new PpCmd.PpCmdPrintBreak(0, 0)] }

export function mt() : PpCmds { return [] }

function spc() : PpCmds { return [new PpCmd.PpCmdPrintBreak(1, 0)] }

export function str(s : string) : PpCmds { return [new PpCmd.PpCmdPrint(new StrToken.StrDef(s))] }

function surround(p : PpCmds) : PpCmds {
  return hov(1, ([] as PpCmds).concat(str('('), p, str(')')))
}

function openTag(t : PpCmd.Tag) : PpCmds { return [new PpCmd.PpCmdOpenTag(t)] }
function closeTag(t : PpCmd.Tag) : PpCmds { return [new PpCmd.PpCmdCloseTag()] }
export function tag(t : PpCmd.Tag, s : PpCmds) : PpCmds {
  return ([] as PpCmds).concat(openTag(t), s, closeTag(t))
}

function isMt(p : PpCmds) : boolean {
  return (p.length === 0)
}

export function tab() : PpCmds { return [new PpCmd.PpCmdSetTab()] }
export function fnl() : PpCmds { return [new PpCmd.PpCmdForceNewline()] }
export function brk(a : number, b : number) : PpCmds { return [new PpCmd.PpCmdPrintBreak(a, b)] }
export function tbrk(a : number, b : number) : PpCmds { return [new PpCmd.PpCmdPrintTbreak(a, b)] }

function PpCmdOfBox(b : PpBox, s : PpCmds) : PpCmds {
  if (b instanceof PpHB) { return h(b.n, s) }
  if (b instanceof PpHoVB) { return hov(b.n, s) }
  if (b instanceof PpHVB) { return hv(b.n, s) }
  if (b instanceof PpVB) { return v(b.n, s) }
  if (b instanceof PpTB) { return t(s) }
  throw MatchFailure('PpCmdOfBox', b)
}

function PpCmdOfCut(c : PpCut) : PpCmds {
  if (c instanceof PpTab) { return tab() }
  if (c instanceof PpFnl) { return fnl() }
  if (c instanceof PpBrk) { return brk(c.n1, c.n2) }
  if (c instanceof PpTbrk) { return tbrk(c.n1, c.n2) }
  throw MatchFailure('PpCmdOfCut', c)
}

function prComAt(n : number) : PpCmds { return mt() }

function prId(id : string) : PpCmds { return str(id) }

function prLIdent([loc, id] : [any, string]) {
  // TODO : Loc.is_ghost
  return prId(id)
}

function prLocated<T>(pr : (t : T) => PpCmds, [loc, x] : Located<T>) {
  // TODO : Flags.beautify?
  return pr(x)
}

function prName(n : NameBase) {
  if (n instanceof Anonymous) {
    return str('_')
  }
  if (n instanceof Name) {
    return prId(n.id)
  }
  throw MatchFailure('prName', n)
}

function prLName([l, n] : Located<NameBase>) : PpCmds {
  if (n instanceof Name) {
    return peaCoqBox(prLIdent([l, n.id]))
  } else {
    return peaCoqBox(prLocated(prName, [l, n]))
  }
}

function surroundImpl(k : BindingKind, p : PpCmds) : PpCmds {
  if (k instanceof Explicit) { return ([] as PpCmds).concat(str('('), p, str(')')) }
  if (k instanceof Implicit) { return ([] as PpCmds).concat(str('{'), p, str('}')) }
  throw MatchFailure('surroundImpl', k)
}

function surroundImplicit(k : BindingKind, p : PpCmds) : PpCmds {
  if (k instanceof Explicit) { return p }
  if (k instanceof Implicit) { return ([] as PpCmds).concat(str('{'), p, str('}')) }
  throw MatchFailure('surroundImplicit', k)
}

function prBinder(
  many : boolean,
  pr : (c : ConstrExpr) => PpCmds,
  [nal, k, t] : [Array<Located<NameBase>>, BinderKind, ConstrExpr]
) : PpCmds {
  if (k instanceof Generalized) {
    const [b, bp, tp] = [k.kind1, k.kind2, k.b]
    throw 'TODO : prBinder Generalized'
  }
  if (k instanceof Default) {
    const b = k.kind
    if (t instanceof CHole) {
      throw 'TODO : prBinder CHole'
    } else {
      const s = ([] as PpCmds).concat(
        prListWithSep(spc, prLName, nal),
        str(' : '),
        pr(t)
      )
      if (many) {
        return peaCoqBox(surroundImpl(b, s))
      } else {
        return peaCoqBox(surroundImplicit(b, s))
      }
    }
  }
  throw MatchFailure('prBinder', k)
}

function prDelimitedBinders(
  kw : () => PpCmds,
  sep : () => PpCmds,
  prC : (t : ConstrExpr) => PpCmds,
  bl : LocalBinder[]
) : PpCmds {
  const n = beginOfBinders(bl)
  if (bl.length === 0) { throw 'prDelimitedBinders : bl should not be empty' }
  const bl0 = bl[0]
  if (bl0 instanceof LocalRawAssum) {
    if (bl.length === 1) {
      const [nal, k, t] : [Array<Located<NameBase>>, BinderKind, ConstrExpr] = [bl0.names, bl0.binderKind, bl0.term]
      return (([] as PpCmds).concat(prComAt(n), kw(), prBinder(false, prC, [nal, k, t])))
    } else {
      return (([] as PpCmds).concat(prComAt(n), kw(), prUndelimitedBinders(sep, prC, bl)))
    }
  } else {
    throw 'prDelimitedBinders : bl should only contain LocalRawAssum'
  }
}

function tagEvar(p : PpCmds) : PpCmds { return tag('evar', p) }
function tagKeyword(p : PpCmds) : PpCmds { return tag('keyword', p) }
function tagNotation(r : PpCmds) : PpCmds { return tag('notation', r) }
function tagPath(p : PpCmds) : PpCmds { return tag('path', p) }
function tagRef(r : PpCmds) : PpCmds { return tag('reference', r) }
function tagType(r : PpCmds) : PpCmds { return tag('univ', r) }
function tagVariable(p : PpCmds) : PpCmds { return tag('variable', p) }

function keyword(s : string) : PpCmds { return tagKeyword(str(s)) }

function prForall() : PpCmds {
  return ([] as PpCmds).concat(keyword('forall'), spc())
}

function prFun() : PpCmds {
  return ([] as PpCmds).concat(keyword('fun'), spc())
}

const maxInt = 9007199254740991

function prListSepLastSep<T>(
  noEmpty : boolean,
  sep : () => PpCmds,
  lastSep : () => PpCmds,
  elem : (t : T) => PpCmds,
  l : T[]
) : PpCmds {
  function start(ll : T[]) : PpCmds {
    if (ll.length === 0) {
      return mt()
    } else if (length === 1) {
      return elem(ll[0])
    } else {
      const [h, t] : [T, T[]] = [ll[0], _.tail(ll)]
      const e = elem(h)
      if (noEmpty && isMt(e)) {
        return start(t)
      } else {
        const aux : (l : T[]) => PpCmds =
          fix((aux : any) => (lll : T[]) => {
            if (lll.length === 0) {
              return mt()
            } else {
              const [h, t] : [T, T[]] = [lll[0], _.tail(lll)]
              const e = elem(h)
              const r = aux(t)
              if (noEmpty && isMt(e)) {
                return r
              } else {
                if (isMt(r)) {
                  return ([] as PpCmds).concat(lastSep(), e)
                } else {
                  return ([] as PpCmds).concat(sep(), e, r)
                }
              }
            }
          })
        // const aux : (l : T[]) => PpCmds = function aux(l : T[]) : PpCmds {
        //   if (l.length === 0) {
        //     return mt()
        //   } else {
        //     const [h, t] : [T, T[]] = [l[0], _.tail(l)]
        //     const e = elem(h)
        //     const r = aux(t)
        //     if (noEmpty && isMt(e)) {
        //       return r
        //     } else {
        //       if (isMt(r)) {
        //         return ([] as PpCmds).concat(lastSep(), e)
        //       } else {
        //         return ([] as PpCmds).concat(sep(), e, r)
        //       }
        //     }
        //   }
        // }
        return ([] as PpCmds).concat(e, aux(t))
      }
    }
  }
  return start(l)
}

function prListWithSep<T>(sep : () => PpCmds, pr : (t : T) => PpCmds, l : T[]) {
  return prListSepLastSep(false, sep, sep, pr, l)
}

function prBinderAmongMany(
  prC : (t : ConstrExpr) => PpCmds,
  b : LocalBinder
) : PpCmds {
  if (b instanceof LocalRawAssum) {
    const [nal, k, t] : [Array<Located<NameBase>>, BinderKind, ConstrExpr] = [b.names, b.binderKind, b.term]
    return prBinder(true, prC, [nal, k, t])
  }
  if (b instanceof LocalRawDef) {
    const [na, c] : [Located<NameBase>, ConstrExpr] = [b.binderName, b.binderType]
    // const cp, topt

    /* TODO :
    if (c instanceof CCast) {
      throw 'TODO : prBinderAmongMany then'
    } else {
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
  sep : () => PpCmds,
  prC : (t : ConstrExpr) => PpCmds,
  l : LocalBinder[]
) {
  return prListWithSep(sep, (b) => prBinderAmongMany(prC, b), l)
}

function prBindersGen(
  prC : (t : ConstrExpr) => PpCmds,
  sep : () => PpCmds,
  isOpen : boolean,
  ul : LocalBinder[]
) {
  if (isOpen) {
    return prDelimitedBinders(mt, sep, prC, ul)
  } else {
    return prUndelimitedBinders(sep, prC, ul)
  }
}

function tagUnparsing(unp : Unparsing, pp1 : PpCmds) : PpCmds {
  if (unp instanceof UnpTerminal) {
    return tagNotation(pp1)
  }
  return pp1
}

function printHunks(
  n : number,
  pr : (_1 : [number, ParenRelation], _2 : ConstrExpr) => PpCmds,
  prBinders : (_1 : () => PpCmds, _2 : boolean, _3 : ConstrExpr) => PpCmds,
  [terms, termlists, binders] : ConstrNotationSubstitution,
  unps : Unparsing[]
) : PpCmds {
  const env : ConstrExpr[] = terms.slice(0)
  const envlist : ConstrExpr[][] = termlists.slice(0)
  const bll : LocalBinder[][] = binders.slice(0)
  function pop<T>(a : T[]) : T {
    const res = a.shift()
    if (res === undefined) {
      debugger
      throw a
    }
    return res
  }
  function ret(unp : Unparsing, pp1 : PpCmds, pp2 : PpCmds) : PpCmds {
    return ([] as PpCmds).concat(tagUnparsing(unp, pp1), pp2)
  }
  function aux(ul : Unparsing[]) : PpCmds {
    if (ul.length === 0) {
      return mt()
    }
    const unp = ul[0]
    const l = _.tail(ul)
    if (unp instanceof UnpMetaVar) {
      const prec = unp.parenRelation
      const c = pop(env)
      const pp2 = aux(l)
      const pp1 = pr([n, prec], c)
      return ret(unp, pp1, pp2)
    }
    if (unp instanceof UnpListMetaVar) {
      const [prec, sl] : [ParenRelation, Unparsing[]] = [unp.parenRelation, unp.unparsing]
      const cl = pop(envlist)
      const pp1 = prListWithSep(
        () => aux(sl),
        x => pr([n, prec], x),
        cl
      )
      const pp2 = aux(l)
      return ret(unp, pp1, pp2)
    }
    if (unp instanceof UnpBinderListMetaVar) {
      const [isOpen, sl] : [boolean, Unparsing[]] = [unp.isOpen, unp.unparsing]
      const cl = pop(bll)
      const pp2 = aux(l)
      const pp1 = prBinders(() => aux(sl), isOpen, cl)
      return ret(unp, pp1, pp2)
    }
    if (unp instanceof UnpTerminal) {
      const s = unp.terminal
      const pp2 = aux(l)
      const pp1 = str(s)
      return ret(unp, pp1, pp2)
    }
    if (unp instanceof UnpBox) {
      const [b, sub] : [PpBox, Unparsing[]] = [unp.box, unp.unparsing]
      const pp1 = PpCmdOfBox(b, aux(sub))
      const pp2 = aux(l)
      return ret(unp, pp1, pp2)
    }
    if (unp instanceof UnpCut) {
      const pp2 = aux(l)
      const pp1 = PpCmdOfCut(unp.cut)
      return ret(unp, pp1, pp2)
    }
    throw MatchFailure('printHunks', unp)
  }
  return aux(unps)
}

type PpResult = [PpCmds, number]

// Here Coq would consult the notation table to figure [unpl] and [level] from
// [s], but we have it already figured out.
function prNotation(
  pr : (_1 : [number, ParenRelation], _2 : ConstrExpr) => PpCmds,
  prBinders : (_1 : () => PpCmds, _2 : boolean, _3 : LocalBinder[]) => PpCmds,
  s : Notation,
  env : ConstrNotationSubstitution,
  // these extra arguments are PeaCoq-specific
  unpl : Unparsing[],
  level : number
) : PpResult {
  return [
    printHunks(level, pr, prBinders, env, unpl),
    level
  ]
}

function reprQualid(sp : QualId) : QualId { return sp }

function prList<T>(pr : (t : T) => PpCmds, l : T[]) : PpCmds {
  return _.reduce(l, (acc, elt) => { return acc.concat(pr(elt)) }, mt())
}

function prQualid(sp : QualId) : PpCmds {
  const [sl0, id0] = reprQualid(sp)
  const id = tagRef(str(id0))
  const rev = sl0.slice(0).reverse()
  const sl : PpCmd[] = (
    (rev.length === 0)
      ? mt()
      : prList(
        (dir : string) => ([] as PpCmds).concat(tagPath(str(dir)), str('.')),
        sl0
      )
  )
  return ([] as PpCmds).concat(sl, id)
}

function prReference(r : Reference) : PpCmds {
  if (r instanceof Qualid) { return peaCoqBox(prQualid(r.lQualid[1])) }
  if (r instanceof Ident) { return peaCoqBox(tagVariable(str(r.id[1]))) }
  throw MatchFailure('prReference', r)
}

function prGlobSortInstance<T>(i : IGlobSortGen<T>) : PpCmds {
  if (i instanceof GProp) { return tagType(str('Prop')) }
  if (i instanceof GSet) { return tagType(str('Set')) }
  if (i instanceof GType) {
    // TODO : this is weird, it's not a Maybe, probably a bug here
    return i.type.caseOf({
      nothing : () => tagType(str('Type')),
      just : (t : string) => str(t),
    })
  }
  throw MatchFailure('prGlobSortInstance', i)
}

function prOptNoSpc<T>(pr : (t : T) => PpCmds, mx : Maybe<T>) : PpCmds {
  return mx.caseOf({
    nothing : () => mt(),
    just : x => pr(x),
  })
}

function prUnivAnnot<T>(pr : (t : T) => PpCmds, x : T) : PpCmds {
  return ([] as PpCmds).concat(str('@{'), pr(x), str('}'))
}

function prUniverseInstance(us : Maybe<InstanceExpr>) : PpCmds {
  return prOptNoSpc(
    x => {
      return prUnivAnnot(
        y => prListWithSep(spc, prGlobSortInstance, y),
        x
      )
    },
    us
  )
}

function prCRef(r : Reference, us : Maybe<InstanceExpr>) : PpCmds {
  return ([] as PpCmds).concat(prReference(r), prUniverseInstance(us))
}

function chop<T>(i : number, l : T[]) : [T[], T[]] {
  return [l.slice(0, i), l.slice(i)]
}

function sepLast<T>(l : T[]) : [T, T[]] {
  const len = l.length
  return [l[len - 1], l.slice(0, len - 1)]
}

function prProj(
  pr : (_1 : ConstrExpr, _2 : ConstrExpr) => PpCmds,
  prApp : (
    pr : (_1 : PrecAssoc, _2 : ConstrExpr) => PpCmds,
    a : ConstrExpr,
    l : AppArgs
  ) => PpCmds,
  a : ConstrExpr,
  f : ConstrExpr,
  l : AppArgs
) : PpCmds {
  return ([] as PpCmds).concat(
    pr([lProj, new E()], a),
    cut(),
    str('.('),
    prApp(pr, f, l),
    str(')')
  )
}

function prExplArgs(
  pr : (pa : PrecAssoc, ce : ConstrExpr) => PpCmds,
  [a, mexpl] : AppArg
) : PpCmds {
  return mexpl.caseOf({
    nothing : () => pr([lApp, new L()], a),
    just : expl => {
      const e = expl.some[1]
      if (e instanceof ExplByPos) {
        throw 'Anomaly : Explicitation by position not implemented'
      }
      if (e instanceof ExplByName) {
        return ([] as PpCmds).concat(str('('), prId(e.name), str(' :='), pr(lTop, a), str(')'))
      }
      throw MatchFailure('prExplArgs', e)
    },
  })
}

function prApp(
  pr : (_1 : PrecAssoc, _2 : ConstrExpr) => PpCmds,
  a : ConstrExpr,
  l : AppArgs
) {
  return (([] as PpCmds).concat(
    pr([lApp, new L()], a),
    prList(x => { return ([] as PpCmds).concat(spc(), prExplArgs(pr, x)) }, l)
  ))
}

function precOfPrimToken(t : PrimToken) : number {
  if (t instanceof Numeral) {
    if (t.numeral >= 0) { return lPosInt } else { return lNegInt }
  }
  if (t instanceof PrimTokenString) {
    return lAtom
  }
  throw MatchFailure('precOfPrimToken', t)
}

function qs(s : string) : PpCmds { return str('\'' + s + '\'') }

function prPrimToken(t : PrimToken) : PpCmds {
  if (t instanceof Numeral) {
    return str(t.numeral.toString())
  }
  if (t instanceof PrimTokenString) {
    return qs(t.str)
  }
  throw MatchFailure('prPrimToken', t)
}

function prUniv(l : string[]) {
  if (l.length === 1) {
    return str(l[0])
  } else {
    return ([] as PpCmds).concat(
      str('max('),
      prListWithSep(() => str(','), str, l),
      str(')')
    )
  }
}

function prGlobSort(s : GlobSort) : PpCmds {
  if (s instanceof GProp) {
    return tagType(str('Prop'))
  }
  if (s instanceof GSet) {
    return tagType(str('Set'))
  }
  if (s instanceof GType) {
    if (s.type.length === 0) {
      return tagType(str('Type'))
    } else {
      return hov(
        0,
        ([] as PpCmds).concat(tagType(str('Type')), prUnivAnnot(prUniv, s.type))
      )
    }
  }
  throw MatchFailure('prGlobSort', s)
}

function prDelimiters(key : string, strm : PpCmds) : PpCmds {
  return peaCoqBox(([] as PpCmds).concat(strm, str('%' + key)))
}

function tagConstrExpr(ce : ConstrExpr, cmds : PpCmds) {
  return peaCoqBox(cmds)
}

function prDanglingWithFor(
  sep : () => PpCmds,
  pr : (_1 : () => PpCmds, _2 : PrecAssoc, _3 : ConstrExpr) => PpCmds,
  inherited : PrecAssoc,
  a : ConstrExpr
) : PpCmds {
  // TODO CFix and CCoFix
  return pr(sep, inherited, a)
}

function casesPatternExprLoc(p : CasesPatternExpr) : CoqLocation {
  // if (p instanceof CPatAlias) { return p.location }
  if (p instanceof CPatCstr) { return p.location }
  if (p instanceof CPatAtom) { return p.location }
  // if (p instanceof CPatOr) { return p.location }
  if (p instanceof CPatNotation) { return p.location }
  // if (p instanceof CPatRecord) { return p.location }
  if (p instanceof CPatPrim) { return p.location }
  if (p instanceof CPatDelimiters) { return p.location }
  throw MatchFailure('casesPatternExprLoc', p)
}

function prWithComments(
  loc : CoqLocation,
  pp : PpCmds
) : PpCmds {
  return prLocated(x => x, [loc, pp])
}

function prPatt(
  sep : () => PpCmds,
  inh : PrecAssoc,
  p : ConstrExpr
) : PpCmds {

  function match(pp : ConstrExpr) : [PpCmds, number] {
    // TODO CPatRecord
    // TODO CPatAlias
    if (pp instanceof CPatCstr) {
      return pp.cases1.caseOf<[PpCmds, number]>({
        nothing : () => {
          if (pp.cases2.length === 0) {
            return [prReference(pp.reference), lAtom]
          } else {
            return [
              ([] as PpCmds).concat(
                prReference(pp.reference),
                prList(
                  x => prPatt(spc, [lApp, new L()], x),
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
              ([] as PpCmds).concat(
                str('@'),
                prReference(pp.reference),
                prList(
                  x => prPatt(spc, [lApp, new L()], x),
                  cases1
                )
              ),
              lApp
            ]
          }
          return [
            ([] as PpCmds).concat(
              surround(([] as PpCmds).concat(
                str('@'),
                prReference(pp.reference),
                prList(
                  x => prPatt(spc, [lApp, new L()], x),
                  cases1
                )
              )),
              prList(
                x => prPatt(spc, [lApp, new L()], x),
                pp.cases2
              )
            ),
            lApp
          ]
        },
      })
    } else if (pp instanceof CPatAtom) {
      const r = pp.reference
      return r.caseOf<PpResult>({
        nothing : () => [str('_'), lAtom],
        just : r => [prReference(r), lAtom],
      })
      // } else if (p instanceof CPatOr) {
      // TODO
    } else if (pp instanceof CPatNotation) {
      if (
        pp.notation === '( _ )'
        && pp.substitution[0].length === 1
        && pp.substitution[1].length === 0
        && pp.patterns.length === 0
      ) {
        return [
          ([] as PpCmds).concat(
            prPatt(() => str('('), [Number.MAX_VALUE, new E()], pp),
            str(')')
          )
          , lAtom
        ]
      } else {
        const s = pp.notation
        const [l, ll] = pp.substitution
        const args = pp.patterns
        const [strmNot, lNot] = prNotation(
          (x, y) => prPatt(mt, x, y),
          (x, y, z) => mt(),
          s,
          [l, ll, []],
          pp.unparsing,
          pp.precedence
        )
        const prefix =
          (args.length === 0 || precLess(lNot, [lApp, new L()]))
            ? strmNot
            : surround(strmNot)
        return [
          ([] as PpCmds).concat(prefix, prList(x => prPatt(spc, [lApp, new L()], x), args)),
          args.length === 0 ? lNot : lApp
        ]
      }
    } else if (pp instanceof CPatPrim) {
      return [prPrimToken(pp.token), lAtom]
    } else if (pp instanceof CPatDelimiters) {
      return [
        prDelimiters(pp.str, prPatt(mt, lSimplePatt, pp.cases)),
        1
      ]
    } else {
      throw MatchFailure('prPatt > match', pp)
    }
  }

  const [strm, prec] : [PpCmds, number] = match(p)
  const loc = casesPatternExprLoc(p)
  return prWithComments(loc, ([] as PpCmds).concat(
    sep(),
    precLess(prec, inh) ? strm : surround(strm)
  ))
}

function prAsin(
  pr : (_1 : PrecAssoc, _2 : ConstrExpr) => PpCmds,
  [mna, indnalopt] : [Maybe<[CoqLocation, NameBase]>, Maybe<ConstrExpr>]
) : PpCmds {
  const prefix = mna.caseOf({
    nothing : () => mt(),
    just : na => ([] as PpCmds).concat(
      spc(),
      keyword('as'),
      spc(),
      prLName(na)
    ),
  })
  const suffix = indnalopt.caseOf({
    nothing : () => mt(),
    just : i => ([] as PpCmds).concat(
      spc(),
      keyword('in'),
      spc(),
      prPatt(mt, lSimplePatt, i)
    ),
  })
  return ([] as PpCmds).concat(
    prefix,
    suffix
  )
}

function prCaseItem(
  pr : (_1 : PrecAssoc, _2 : ConstrExpr) => PpCmds,
  [tm, asin] : [ConstrExpr, [Maybe<[CoqLocation, NameBase]>, Maybe<ConstrExpr>]]
) : PpCmds {
  return hov(0, ([] as PpCmds).concat(
    pr([lCast, new E()], tm),
    prAsin(pr, asin)
  ))
}

function sepV() : PpCmds { return ([] as PpCmds).concat(str(','), spc()) }

function constrLoc(c : ConstrExpr) : CoqLocation {
  if (c instanceof CRef) {
    const ref = c.reference
    if (ref instanceof Ident) {
      return ref.id[0]
    }
    if (ref instanceof Qualid) {
      return ref.lQualid[0]
    }
    throw MatchFailure('constrLoc', ref)
  }
  // if (c instanceof CFix) { return c.location }
  // if (c instanceof CCoFix) { return c.location }
  if (c instanceof CProdN) { return c.location }
  if (c instanceof CLambdaN) { return c.location }
  if (c instanceof CLetIn) { return c.location }
  // if (c instanceof CAppExpl) { return c.location }
  if (c instanceof CApp) { return c.location }
  // if (c instanceof CRecord) { return c.location }
  if (c instanceof CCases) { return c.location }
  if (c instanceof CLetTuple) { return c.location }
  // if (c instanceof CIf) { return c.location }
  if (c instanceof CHole) { return c.location }
  // if (c instanceof CPatVar) { return c.location }
  // if (c instanceof CEvar) { return c.location }
  if (c instanceof CSort) { return c.location }
  // if (c instanceof CCast) { return c.location }
  if (c instanceof CNotation) { return c.location }
  // if (c instanceof CGeneralization) { return c.location }
  if (c instanceof CPrim) { return c.location }
  if (c instanceof CDelimiters) { return c.location }
  throw MatchFailure('constrLoc', c)
}

function prSepCom(
  sep : () => PpCmds,
  f : (c : ConstrExpr) => PpCmds,
  c : ConstrExpr
) : PpCmds {
  return prWithComments(constrLoc(c), ([] as PpCmds).concat(sep(), f(c)))
}

function prCaseType(
  pr : (_1 : PrecAssoc, _2 : ConstrExpr) => PpCmds,
  mpo : Maybe<ConstrExpr>
) : PpCmds {
  // TODO : po instanceof CHole with IntroAnonymous
  return mpo.caseOf({
    nothing : () => mt(),
    just : po => ([] as PpCmds).concat(
      spc(),
      hov(2, ([] as PpCmds).concat(
        keyword('return'),
        prSepCom(spc, x => pr(lSimpleConstr, x), po)
      ))
    ),
  })
}

function prBar() { return ([] as PpCmds).concat(str(';'), spc()) }

function prEqn(
  pr : (_1 : PrecAssoc, _2 : ConstrExpr) => PpCmds,
  [loc, pl0, rhs] : BranchExpr
) : PpCmds {
  const pl1 = _(pl0).map((located : Located<Array<CasesPatternExpr>>) => located[1]).value()
  return ([] as PpCmds).concat(
    spc(),
    hov(4,
      prWithComments(
        loc,
        ([] as PpCmds).concat(
          str('| '),
          hov(0, ([] as PpCmds).concat(
            prListWithSep(
              prBar,
              x => prListWithSep(sepV, y => prPatt(mt, lTop, y), x),
              pl1
            ),
            str(' =>')
          )),
          prSepCom(spc, x => pr(lTop, x), rhs)
        )
      )
    )
  )
}

function prSimpleReturnType(
  pr : (_1 : PrecAssoc, _2 : ConstrExpr) => PpCmds,
  mna : Maybe<Located<Name>>,
  po : Maybe<ConstrExpr>
) : PpCmds {
  let res = ([] as PpCmds)

  mna.caseOf({
    nothing : () => { res = res.concat(mt()) },
    just : na => {
      const name = na.some[1]
      if (name instanceof Name) {
        res = res.concat(spc(), keyword('as'), spc(), prId(name.id))
      } else {
        res = res.concat(mt)
      }
    },
  })

  res = res.concat(prCaseType(pr, po))

  return res
}

function extractLamBinders(a : ConstrExpr) : [LocalBinder[], ConstrExpr] {
  if (a instanceof CLambdaN) {
    if (a.binders.length === 0) {
      return extractLamBinders(a.body)
    } else {
      const [nal, bk, t] = a.binders[0]
      const [bl, c] = extractLamBinders(a.body)
      const res : LocalBinder[] = [new LocalRawAssum(nal, bk, t)]
      return [res.concat(bl), c]
    }
  } else {
    return [[], a]
  }
}

const prFunSep : PpCmds = ([] as PpCmds).concat(spc(), str('=>'))

function prGen(
  pr : (_1 : () => PpCmds, _2 : PrecAssoc, _3 : ConstrExpr) => PpCmds
) : (_1 : () => PpCmds, _2 : PrecAssoc, _3 : ConstrExpr) => PpCmds {
  return (
    sep : () => PpCmds,
    inherited : PrecAssoc,
    a : ConstrExpr
  ) => {

    function ret(cmds : PpCmds, prec : number) : PpResult {
      return [tagConstrExpr(a, cmds), prec]
    }

    const prmt = (x : [number, ParenRelation], y : ConstrExpr) => pr(mt, x, y)

    function match(aa : ConstrExpr) : PpResult {

      if (aa instanceof CApp) {
        // TODO : ldots_var
        const pf = aa.funct[0]
        const f = aa.funct[1]
        return pf.caseOf<PpResult>({
          nothing : () => {
            const b = <CApp>aa // TS bug
            const [f, l] = [b.funct[1], b.args]
            return ret(prApp(prmt, f, l), lApp)
          },
          just : pf => {
            const b = <CApp>aa // TS bug
            const [i, f, l] = [pf, b.funct[1], b.args]
            const [l1, l2] = chop(i, l)
            const [c, rest] = sepLast(l1)
            // TODO : assert c[1] is empty option?
            const p = prProj(prmt, prApp, c[0], f, rest)
            // TODO : it might be nice if we could highlight the structure
            // nested applications, rather than having a flat n-ary one
            if (l2.length > 0) {
              return ret(
                ([] as PpCmds).concat(
                  p,
                  prList(
                    aaa => {
                      return ([] as PpCmds).concat(spc(), prExplArgs(prmt, aaa))
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

      if (aa instanceof CCases) {
        if (aa.caseStyle instanceof LetPatternStyle) {
          throw 'TODO : LetPatternStyle'
        }
        const prDangling = (pa : [number, ParenRelation], c : ConstrExpr) => prDanglingWithFor(mt, pr, pa, c)
        return ret(
          v(0, hv(0, ([] as PpCmds).concat(
            keyword('match'),
            brk(1, 2),
            hov(0,
              prListWithSep(
                sepV,
                x => prCaseItem(prDangling, x),
                aa.cases
              )
            ),
            prCaseType(prDangling, aa.returnType),
            spc(),
            keyword('with'),
            prList(
              (e : BranchExpr) => prEqn((x, y) => pr(mt, x, y), e),
              aa.branches
            ),
            spc(),
            keyword('end')
          ))),
          lAtom
        )
      }

      if (aa instanceof CDelimiters) {
        const [sc, e] = [aa.str, aa.expr]
        return ret(
          prDelimiters(sc, pr(mt, [lDelim, new E()], e)),
          lDelim
        )
      }

      if (aa instanceof CLambdaN) {
        const [bl, a1] = extractLamBinders(aa)
        return ret(
          hov(0, ([] as PpCmds).concat(
            hov(2, prDelimitedBinders(prFun, spc, x => pr(spc, lTop, x), bl)),
            prFunSep,
            pr(spc, lTop, a1)
          )),
          lLambda
        )
      }

      if (aa instanceof CLetIn) {
        const bound = aa.bound
        if (bound instanceof CFix || bound instanceof CCoFix) {
          throw ('TODO : pr CLetIn with CFix/CcoFix')
        }
        return ret(
          hv(0, ([] as PpCmds).concat(
            hov(2, ([] as PpCmds).concat(
              keyword('let'), spc(), prLName(aa.name), str(' :='),
              pr(spc, lTop, aa.bound), spc(), keyword('in')
            )),
            pr(spc, lTop, aa.body)
          )),
          lLetIn
        )
      }

      if (aa instanceof CLetTuple) {
        return ret(
          hv(0, ([] as PpCmds).concat(
            keyword('let'),
            spc(),
            hov(0, ([] as PpCmds).concat(
              str('('),
              prListWithSep(sepV, prLName, aa.names),
              str(')'),
              prSimpleReturnType(prmt, aa.returnType[0], aa.returnType[1]),
              str(' :='),
              pr(spc, lTop, aa.bound),
              spc(),
              keyword('in')
            )),
            pr(spc, lTop, aa.body)
          )),
          lLetIn
        )
      }

      if (aa instanceof CNotation) {
        if (aa.notation === '(\u00A0_\u00A0)') {
          const [[t], [], []] = aa.substitution
          return ret(
            ([] as PpCmds).concat(
              pr(
                () => { return str('(') },
                [maxInt, new L()],
                t
              ),
              str(')')
            ),
            lAtom
          )
        } else {
          const [s, env] : [Notation, ConstrNotationSubstitution] = [aa.notation, aa.substitution]
          return prNotation(
            (x, y) => pr(mt, x, y),
            (x, y, z) => prBindersGen(w => pr(mt, lTop, w), x, y, z),
            s,
            env,
            aa.unparsing,
            aa.precedence
          )
        }
      }

      if (aa instanceof CPrim) {
        return ret(
          prPrimToken(aa.token),
          precOfPrimToken(aa.token)
        )
      }

      if (aa instanceof CProdN) {
        const [bl, aRest] = extractProdBinders(aa)
        return ret(
          ([] as PpCmds).concat(
            prDelimitedBinders(
              prForall,
              spc,
              x => pr(mt, lTop, x),
              bl),
            str(','),
            pr(spc, lTop, aRest)
          ),
          lProd
        )
      }

      if (aa instanceof CRef) {
        const [r, us] = [aa.reference, aa.universeInstance]
        return ret(
          prCRef(r, us),
          lAtom
        )
      }

      if (aa instanceof CSort) {
        return ret(prGlobSort(aa.globSort), lAtom)
      }

      throw MatchFailure('pr > match', aa)

    }

    const [strm, prec] = match(a)

    let result = (
      precLess(prec, inherited)
        ? sep().concat(strm)
        : sep().concat(surround(strm))
    )
    return result

  }
}

export function prConstrExpr(a : ConstrExpr) : PpCmds {
  return fix(prGen)(mt, lTop, a)
}

function prHTMLGen(
  pr : (_1 : () => PpCmds, _2 : PrecAssoc, _3 : ConstrExpr) => PpCmds
) : (_1 : () => PpCmds, _2 : PrecAssoc, _3 : ConstrExpr) => PpCmds {
  const recur = prGen(pr)
  return (sep : () => PpCmds, pa : PrecAssoc, e : ConstrExpr) => {
    return ([] as PpCmds).concat(
      str(`<span class='ace_editor syntax'>`),
      recur(sep, pa, e),
      str('</span>')
    )
  }
}

function prHTML(a : ConstrExpr) : PpCmds {
  return fix(prHTMLGen)(mt, lTop, a)
}

function dumbPrintPpCmd(p : PpCmd) : string {
  if (p instanceof PpCmd.PpCmdPrint) {
    return dumbPrintStrToken(p.token)
  }
  if (p instanceof PpCmd.PpCmdBox) {
    // FIXME : use blockType
    return dumbPrintPpCmds(p.contents)
  }
  if (p instanceof PpCmd.PpCmdPrintBreak) {
    return ' '.repeat(p.nspaces)
  }
  if (p instanceof PpCmd.PpCmdSetTab) {
    return 'TODO : PpCmdSetTab'
  }
  if (p instanceof PpCmd.PpCmdPrintTbreak) {
    return 'TODO : PpCmdPrintTbreak'
  }
  if (p instanceof PpCmd.PpCmdWhiteSpace) {
    return 'TODO : PpCmdWhiteSpace'
  }
  if (p instanceof PpCmd.PpCmdForceNewline) {
    return 'TODO : PpCmdForceNewline'
  }
  if (p instanceof PpCmd.PpCmdPrintIfBroken) {
    return 'TODO : PpCmdPrintIfBroken'
  }
  if (p instanceof PpCmd.PpCmdOpenBox) {
    return 'TODO : PpCmdOpenBox'
  }
  if (p instanceof PpCmd.PpCmdCloseBox) {
    return 'TODO : PpCmdCloseBox'
  }
  if (p instanceof PpCmd.PpCmdCloseTBox) {
    return 'TODO : PpCmdCloseTBox'
  }
  if (p instanceof PpCmd.PpCmdComment) {
    return 'TODO : PpCmdComment'
  }
  if (p instanceof PpCmd.PpCmdOpenTag) {
    return ''
  }
  if (p instanceof PpCmd.PpCmdCloseTag) {
    return ''
  }
  throw MatchFailure('dumbPrintPpCmd', p)
}

function dumbPrintStrToken(t : StrToken.StrToken) : string {
  if (t instanceof StrToken.StrDef) {
    return t.str
  }
  if (t instanceof StrToken.StrLen) {
    return t.str
  }
  throw MatchFailure('dumbPrintStrToken', t)
}

function dumbPrintPpCmds(l : PpCmds) : string {
  return _.reduce(
    l,
    (acc : string, p : PpCmd) => { return acc + dumbPrintPpCmd(p) },
    ''
  )
}

function ppCmdSameShape(p : PpCmd, old : PpCmd) : boolean {
  return (p.constructor === old.constructor)
}

export function ppCmdsSameShape(l : PpCmds, old : PpCmds) : boolean {
  if (l.length === 0 && old.length === 0) { return true }
  if (l.length > 0 && old.length > 0) {
    return (
      ppCmdSameShape(l[0], old[0])
      && ppCmdsSameShape(l.slice(1), old.slice(1))
    )
  }
  return false
}
