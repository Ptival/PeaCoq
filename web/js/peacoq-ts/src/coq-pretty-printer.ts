import * as BinderKind from "./binder-kind";
import { BindingKind, Explicit, Implicit } from "./binding-kind";
import { PpHBox, PpVBox, PpHVBox, PpHoVBox, PpTBox } from "./block-type";
import { CasesPatternExpr, CPatAtom, CPatCstr, CPatDelimiters, CPatPrim } from "./cases-pattern-expr";
import * as CaseStyle from "./case-style";
import * as ConstrExpr from "./coq-constr-expr";
import { CoqLocation, GlobSort, InstanceExpr, Located } from "./coq-definitions";
import * as Explicitation from "./explicitation";
import { GProp, GSet, GType } from "./glob-sort-gen";
import * as LocalBinder from "./local-binder";
import * as NameBase from "./name-base";
import { Any, E, L, ParenRelation, Prec } from "./paren-relation";
import * as PpBox from "./ppbox";
import * as PpCmd from "./ppcmd-token";
import { PpBrk, PpCut, PpFnl, PpTab, PpTbrk } from "./ppcut";
import * as PrimToken from "./prim-token";
import * as Reference from "./reference";
import * as StrToken from "./str-token";
import {
  Unparsing, UnpBinderListMetaVar, UnpBox, UnpCut, UnpListMetaVar,
  UnpMetaVar, UnpTerminal
} from "./unparsing";

type PpCmd = PpCmd.PpCmdToken<StrToken.StrToken>;
export type PpCmds = PpCmd[];

export type PrecAssoc = [number, ParenRelation];

let lAtom = 0;
let lProd = 200;
let lLambda = 200;
let lIf = 200;
let lLetIn = 200;
let lLetPattern = 200;
let lFix = 200;
let lCast = 100;
let lArg = 9;
let lApp = 10;
let lPosInt = 0;
let lNegInt = 35;
let lTop: PrecAssoc = [200, new E()];
let lProj = 1;
let lDelim = 1;
let lSimpleConstr: PrecAssoc = [8, new E()];
let lSimplePatt: PrecAssoc = [1, new E()];

export function precLess(child: number, parent: PrecAssoc) {
  let [parentPrec, parentAssoc] = parent;
  if (parentPrec < 0 && child === lProd) {
    return true;
  }
  parentPrec = Math.abs(parentPrec);
  if (parentAssoc instanceof E) { return child <= parentPrec; }
  if (parentAssoc instanceof L) { return child < parentPrec; }
  if (parentAssoc instanceof Prec) { return child <= parentAssoc.precedence; }
  if (parentAssoc instanceof Any) { return true; }
}

/*
peaCoqBox should not disrupt the pretty-printing flow, but add a
<span> so that sub-expression highlighting is more accurate
*/
function peaCoqBox(l: PpCmds): PpCmds {
  return [new PpCmd.PpCmdBox(new PpHoVBox(0), l)];
}

export function h(n: number, s: PpCmds): PpCmds { return [new PpCmd.PpCmdBox(new PpHBox(n), s)]; }
export function v(n: number, s: PpCmds): PpCmds { return [new PpCmd.PpCmdBox(new PpVBox(n), s)]; }
export function hv(n: number, s: PpCmds): PpCmds { return [new PpCmd.PpCmdBox(new PpHVBox(n), s)]; }
export function hov(n: number, s: PpCmds): PpCmds { return [new PpCmd.PpCmdBox(new PpHoVBox(n), s)]; }
export function t(s: PpCmds): PpCmds { return [new PpCmd.PpCmdBox(new PpTBox(), s)]; }

function cut(): PpCmds { return [new PpCmd.PpCmdPrintBreak(0, 0)]; }

export function mt(): PpCmds { return []; }

function spc(): PpCmds { return [new PpCmd.PpCmdPrintBreak(1, 0)]; }

export function str(s: string): PpCmds { return [new PpCmd.PpCmdPrint(new StrToken.StrDef(s))]; }

function surround(p: PpCmds): PpCmds {
  return hov(1, [].concat(str("("), p, str(")")));
}

function openTag(t: PpCmd.Tag): PpCmds { return [new PpCmd.PpCmdOpenTag(t)]; }
function closeTag(t: PpCmd.Tag): PpCmds { return [new PpCmd.PpCmdCloseTag()]; }
export function tag(t: PpCmd.Tag, s: PpCmds): PpCmds {
  return [].concat(openTag(t), s, closeTag(t));
}

function isMt(p: PpCmds): boolean {
  return (p.length === 0);
}

export function tab(): PpCmds { return [new PpCmd.PpCmdSetTab()]; }
export function fnl(): PpCmds { return [new PpCmd.PpCmdForceNewline()]; }
export function brk(a, b): PpCmds { return [new PpCmd.PpCmdPrintBreak(a, b)]; }
export function tbrk(a, b): PpCmds { return [new PpCmd.PpCmdPrintTbreak(a, b)]; }

function PpCmdOfBox(b: PpBox.PpBox, s: PpCmds): PpCmds {
  if (b instanceof PpBox.PpHB) { return h(b.n, s); }
  if (b instanceof PpBox.PpHoVB) { return hov(b.n, s); }
  if (b instanceof PpBox.PpHVB) { return hv(b.n, s); }
  if (b instanceof PpBox.PpVB) { return v(b.n, s); }
  if (b instanceof PpBox.PpTB) { return t(s); }
  throw MatchFailure("PpCmdOfBox", b);
}

function PpCmdOfCut(c: PpCut): PpCmds {
  if (c instanceof PpTab) { return tab(); }
  if (c instanceof PpFnl) { return fnl(); }
  if (c instanceof PpBrk) { return brk(c.n1, c.n2); }
  if (c instanceof PpTbrk) { return tbrk(c.n1, c.n2); }
  throw MatchFailure("PpCmdOfCut", c);
}

function prComAt(n: number): PpCmds { return mt(); }

function prId(id: string): PpCmds { return str(id); }

function prLIdent([loc, id]) {
  // TODO: Loc.is_ghost
  return prId(id);
}

function prLocated(pr, [loc, x]) {
  // TODO: Flags.beautify?
  return pr(x);
}

function prName(n: NameBase.NameBase) {
  if (n instanceof NameBase.Anonymous) {
    return str("_");
  }
  if (n instanceof NameBase.Name) {
    return prId(n.id);
  }
  throw MatchFailure("prName", n);
}

function prLName([l, n]: [PpCmds, NameBase.NameBase]): PpCmds {
  if (n instanceof NameBase.Name) {
    return peaCoqBox(prLIdent([l, n.id]));
  } else {
    return peaCoqBox(prLocated(prName, [l, n]));
  }
}

function surroundImpl(k: BindingKind, p: PpCmds): PpCmds {
  if (k instanceof Explicit) { return [].concat(str("("), p, str(")")); }
  if (k instanceof Implicit) { return [].concat(str("{"), p, str("}")); }
  throw MatchFailure("surroundImpl", k);
}

function surroundImplicit(k: BindingKind, p: PpCmds): PpCmds {
  if (k instanceof Explicit) { return p; }
  if (k instanceof Implicit) { return [].concat(str("{"), p, str("}")); }
  throw MatchFailure("surroundImplicit", k);
}

function prBinder(
  many: boolean,
  pr: (c: ConstrExpr.ConstrExpr) => PpCmds,
  [nal, k, t]
): PpCmds {
  if (k instanceof BinderKind.Generalized) {
    let [b, bp, tp] = [k.kind1, k.kind2, k.b];
    throw "TODO: prBinder Generalized";
  }
  if (k instanceof BinderKind.Default) {
    let b = k.kind;
    if (t instanceof ConstrExpr.CHole) {
      throw "TODO: prBinder CHole";
    } else {
      let s = [].concat(
        prListWithSep(spc, prLName, nal),
        str(" : "),
        pr(t)
      );
      if (many) {
        return peaCoqBox(surroundImpl(b, s));
      } else {
        return peaCoqBox(surroundImplicit(b, s));
      }
    }
  }
  throw MatchFailure("prBinder", k);
}

function prDelimitedBinders(
  kw: () => PpCmds,
  sep: () => PpCmds,
  prC: (t: ConstrExpr.ConstrExpr) => PpCmds,
  bl: LocalBinder.LocalBinder[]
): PpCmds {
  let n = LocalBinder.beginOfBinders(bl);
  if (bl.length === 0) { throw "prDelimitedBinders: bl should not be empty"; }
  let bl0 = bl[0];
  if (bl0 instanceof LocalBinder.LocalRawAssum) {
    if (bl.length === 1) {
      let [nal, k, t] = [bl0.names, bl0.binderKind, bl0.term];
      return ([].concat(prComAt(n), kw(), prBinder(false, prC, [nal, k, t])));
    } else {
      return ([].concat(prComAt(n), kw(), prUndelimitedBinders(sep, prC, bl)));
    }
  } else {
    throw "prDelimitedBinders: bl should only contain LocalRawAssum";
  }
}

function tagEvar(p: PpCmds): PpCmds { return tag("evar", p); }
function tagKeyword(p: PpCmds): PpCmds { return tag("keyword", p); }
function tagNotation(r: PpCmds): PpCmds { return tag("notation", r); }
function tagPath(p: PpCmds): PpCmds { return tag("path", p); }
function tagRef(r: PpCmds): PpCmds { return tag("reference", r); }
function tagType(r: PpCmds): PpCmds { return tag("univ", r); }
function tagVariable(p: PpCmds): PpCmds { return tag("variable", p); }

function keyword(s: string): PpCmds { return tagKeyword(str(s)); }

function prForall(): PpCmds {
  return [].concat(keyword("forall"), spc());
}

function prFun(): PpCmds {
  return [].concat(keyword("fun"), spc());
}

let maxInt = 9007199254740991;

function prListSepLastSep<T>(
  noEmpty: boolean,
  sep: () => PpCmds,
  lastSep: () => PpCmds,
  elem: (T) => PpCmds,
  l: T[]
): PpCmds {
  function start(l: T[]): PpCmds {
    if (l.length === 0) {
      return mt();
    } else if (length === 1) {
      return elem(l[0]);
    } else {
      let [h, t] = [l[0], _.tail(l)];
      let e = elem(h);
      if (noEmpty && isMt(e)) {
        return start(t);
      } else {
        function aux(l: T[]): PpCmds {
          if (l.length === 0) {
            return mt();
          } else {
            let [h, t] = [l[0], _.tail(l)];
            let e = elem(h);
            let r = aux(t);
            if (noEmpty && isMt(e)) {
              return r;
            } else {
              if (isMt(r)) {
                return [].concat(lastSep(), e);
              } else {
                return [].concat(sep(), e, r);
              }
            }
          }
        }
        return [].concat(e, aux(t));
      }
    }
  }
  return start(l);
}

function prListWithSep(sep, pr, l) {
  return prListSepLastSep(false, sep, sep, pr, l);
}

function prBinderAmongMany(
  prC,
  b: LocalBinder.LocalBinder
): PpCmds {
  if (b instanceof LocalBinder.LocalRawAssum) {
    let [nal, k, t] = [b.names, b.binderKind, b.term];
    return prBinder(true, prC, [nal, k, t]);
  }
  if (b instanceof LocalBinder.LocalRawDef) {
    let [na, c] = [b.binderName, b.binderType];
    let cp, topt;

    /* TODO:
    if (c instanceof CCast) {
      throw "TODO: prBinderAmongMany then";
    } else {
      throw "TODO: prBinderAmongMany else"
    }
    */

    throw "TODO: prBinderAmongMany";
  }
}

function prUndelimitedBinders(sep, prC, l) {
  return prListWithSep(sep, (b) => prBinderAmongMany(prC, b), l);
}

function prBindersGen(
  prC,
  sep: () => PpCmds,
  isOpen: boolean,
  ul: LocalBinder.LocalBinder[]
) {
  if (isOpen) {
    return prDelimitedBinders(mt, sep, prC, ul);
  } else {
    return prUndelimitedBinders(sep, prC, ul);
  }
}

function tagUnparsing(unp: Unparsing, pp1: PpCmds): PpCmds {
  if (unp instanceof UnpTerminal) {
    return tagNotation(pp1);
  }
  return pp1;
}

function printHunks(
  n,
  pr: (_1: [number, ParenRelation], _2: ConstrExpr.ConstrExpr) => PpCmds,
  prBinders: (_1: () => PpCmds, _2: boolean, _3: ConstrExpr.ConstrExpr) => PpCmds,
  [terms, termlists, binders]: ConstrExpr.ConstrNotationSubstitution,
  unps: Unparsing[])
  : PpCmds {
  let env = terms.slice(0);
  let envlist = termlists.slice(0);
  let bll = binders.slice(0);
  function pop(a: ConstrExpr.ConstrExpr[]): ConstrExpr.ConstrExpr { return a.shift(); }
  function ret(unp: Unparsing, pp1: PpCmds, pp2: PpCmds): PpCmds {
    return [].concat(tagUnparsing(unp, pp1), pp2);
  }
  function aux(ul: Unparsing[]): PpCmds {
    let pp1: PpCmds;
    let pp2: PpCmds;
    if (ul.length === 0) {
      return mt();
    }
    let unp = ul[0];
    let l = _.tail(ul);
    if (unp instanceof UnpMetaVar) {
      let prec = unp.parenRelation;
      let c = pop(env);
      pp2 = aux(l);
      pp1 = pr([n, prec], c);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpListMetaVar) {
      let [prec, sl] = [unp.parenRelation, unp.unparsing];
      let cl = pop(envlist);
      pp1 = prListWithSep(
        () => aux(sl),
        (x) => pr([n, prec], x),
        cl
      );
      pp2 = aux(l);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpBinderListMetaVar) {
      let [isOpen, sl] = [unp.isOpen, unp.unparsing];
      let cl = pop(bll);
      pp2 = aux(l);
      pp1 = prBinders(() => aux(sl), isOpen, cl);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpTerminal) {
      let s = unp.terminal;
      pp2 = aux(l);
      pp1 = str(s);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpBox) {
      let [b, sub] = [unp.box, unp.unparsing];
      pp1 = PpCmdOfBox(b, aux(sub));
      pp2 = aux(l);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpCut) {
      pp2 = aux(l);
      pp1 = PpCmdOfCut(unp.cut);
      return ret(unp, pp1, pp2);
    }
    throw MatchFailure("printHunks", unp);
  }
  return aux(unps);
}

type PpResult = [PpCmds, number];

// Here Coq would consult the notation table to figure [unpl] and [level] from
// [s], but we have it already figured out.
function prNotation(
  pr, prBinders, s,
  env: ConstrExpr.ConstrNotationSubstitution,
  unpl: Unparsing[],
  level: number
): PpResult {
  return [
    printHunks(level, pr, prBinders, env, unpl),
    level
  ];
}

function reprQualid(sp: Reference.QualId): Reference.QualId { return sp; }

function prList<T>(pr: (t: T) => PpCmds, l: T[]): PpCmds {
  return _.reduce(l, (acc, elt) => { return acc.concat(pr(elt)); }, mt());
}

function prQualid(sp: Reference.QualId): PpCmds {
  let [sl0, id0] = reprQualid(sp);
  let id = tagRef(str(id0));
  let rev = sl0.slice(0).reverse();
  let sl: PpCmd[];
  if (rev.length === 0) {
    sl = mt();
  } else {
    sl = prList(
      (dir: string) => [].concat(tagPath(str(dir)), str(".")),
      sl0
    );
  }
  return [].concat(sl, id);
}

function prReference(r: Reference.Reference): PpCmds {
  if (r instanceof Reference.Qualid) { return peaCoqBox(prQualid(r.lQualid[1])); }
  if (r instanceof Reference.Ident) { return peaCoqBox(tagVariable(str(r.id[1]))); }
  throw MatchFailure("prReference", r);
}

function prGlobSortInstance(i): PpCmds {
  if (i instanceof GProp) { return tagType(str("Prop")); }
  if (i instanceof GSet) { return tagType(str("Set")); }
  if (i instanceof GType) {
    return i.type.caseOf({
      nothing: () => tagType(str("Type")),
      just: (t) => str(t),
    });
  }
  throw MatchFailure("prGlobSortInstance", i);
}

function prOptNoSpc<T>(pr: (T) => PpCmds, x: Maybe<T>): PpCmds {
  return x.caseOf({
    nothing: () => mt(),
    just: (x) => pr(x),
  });
}

function prUnivAnnot<T>(pr: (T) => PpCmds, x: T): PpCmds {
  return [].concat(str("@{"), pr(x), str("}"));
}

function prUniverseInstance(us: Maybe<InstanceExpr>): PpCmds {
  return prOptNoSpc(
    (x) => {
      return prUnivAnnot(
        (y) => prListWithSep(spc, prGlobSortInstance, y),
        x
      );
    },
    us
  );
}

function prCRef(r: Reference.Reference, us: Maybe<InstanceExpr>): PpCmds {
  return [].concat(prReference(r), prUniverseInstance(us));
}

function chop<T>(i: number, l: T[]): [T[], T[]] {
  return [l.slice(0, i), l.slice(i)];
}

function sepLast<T>(l: T[]): [T, T[]] {
  let len = l.length;
  return [l[len - 1], l.slice(0, len - 1)];
}

function prProj(
  pr: (_1, _2: ConstrExpr.ConstrExpr) => PpCmds,
  prApp,
  a: ConstrExpr.ConstrExpr,
  f,
  l
): PpCmds {
  return [].concat(
    pr([lProj, new E()], a),
    cut(),
    str(".("),
    prApp(pr, f, l),
    str(")")
  );
}

function prExplArgs(
  pr: (pa: PrecAssoc, ce: ConstrExpr.ConstrExpr) => PpCmds,
  [a, expl]: ConstrExpr.AppArg
): PpCmds {
  return expl.caseOf({
    nothing: () => pr([lApp, new L()], a),
    just: (expl) => {
      let e = expl.some[1];
      if (e instanceof Explicitation.ExplByPos) {
        throw "Anomaly: Explicitation by position not implemented";
      }
      if (e instanceof Explicitation.ExplByName) {
        return [].concat(str("("), prId(e.name), str(":="), pr(lTop, a), str(")"));
      }
      throw MatchFailure("prExplArgs", e);
    },
  });
}

function prApp(
  pr: (_1: PrecAssoc, _2: ConstrExpr.ConstrExpr) => PpCmds,
  a: ConstrExpr.ConstrExpr,
  l: ConstrExpr.AppArgs
) {
  return ([].concat(
    pr([lApp, new L()], a),
    prList((x) => { return [].concat(spc(), prExplArgs(pr, x)); }, l)
  ));
}

function precOfPrimToken(t: PrimToken.PrimToken): number {
  if (t instanceof PrimToken.Numeral) {
    if (t.numeral >= 0) { return lPosInt; } else { return lNegInt; }
  }
  if (t instanceof PrimToken.PrimTokenString) {
    return lAtom;
  }
  throw MatchFailure("precOfPrimToken", t);
}

function qs(s: string): PpCmds { return str("\"" + s + "\""); }

function prPrimToken(t: PrimToken.PrimToken): PpCmds {
  if (t instanceof PrimToken.Numeral) {
    return str(t.numeral.toString());
  }
  if (t instanceof PrimToken.PrimTokenString) {
    return qs(t.string);
  }
  throw MatchFailure("prPrimToken", t);
}

function prUniv(l) {
  if (l.length === 1) {
    return str(l[0]);
  } else {
    return [].concat(
      str("max("),
      prListWithSep(() => str(","), str, l),
      str(")")
    );
  }
}

function prGlobSort(s: GlobSort): PpCmds {
  if (s instanceof GProp) {
    return tagType(str("Prop"));
  }
  if (s instanceof GSet) {
    return tagType(str("Set"));
  }
  if (s instanceof GType) {
    if (s.type.length === 0) {
      return tagType(str("Type"));
    } else {
      return hov(
        0,
        [].concat(tagType(str("Type")), prUnivAnnot(prUniv, s.type))
      );
    }
  }
  throw MatchFailure("prGlobSort", s);
}

function prDelimiters(key: string, strm: PpCmds): PpCmds {
  return peaCoqBox([].concat(strm, str("%" + key)));
}

function tagConstrExpr(ce: ConstrExpr.ConstrExpr, cmds: PpCmds) {
  return peaCoqBox(cmds);
}

function prDanglingWithFor(
  sep: () => PpCmds,
  pr: (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr.ConstrExpr) => PpCmds,
  inherited: PrecAssoc,
  a: ConstrExpr.ConstrExpr
): PpCmds {
  // TODO CFix and CCoFix
  return pr(sep, inherited, a);
}

function casesPatternExprLoc(p): CoqLocation {
  // if (p instanceof CPatAlias) { return p.location; }
  if (p instanceof CPatCstr) { return p.location; }
  if (p instanceof CPatAtom) { return p.location; }
  // if (p instanceof CPatOr) { return p.location; }
  // if (p instanceof CPatNotation) { return p.location; }
  // if (p instanceof CPatRecord) { return p.location; }
  if (p instanceof CPatPrim) { return p.location; }
  if (p instanceof CPatDelimiters) { return p.location; }
  throw MatchFailure("casesPatternExprLoc", p);
}

function prWithComments(
  loc: CoqLocation,
  pp
): PpCmds {
  return prLocated((x) => x, [loc, pp]);
}

function prPatt(
  sep: () => PpCmds,
  inh: PrecAssoc,
  p: ConstrExpr.ConstrExpr
): PpCmds {

  function match(p: ConstrExpr.ConstrExpr): [PpCmds, number] {
    // TODO CPatRecord
    // TODO CPatAlias
    if (p instanceof CPatCstr) {
      if (p.cases1.length === 0 && p.cases2.length === 0) {
        return [prReference(p.reference), lAtom];
      }
      if (p.cases1.length === 0) {
        return [
          [].concat(
            prReference(p.reference),
            prList(
              (x) => prPatt(spc, [lApp, new L()], x),
              p.cases2
            )
          ),
          lApp
        ];
      }
      if (p.cases2.length === 0) {
        return [
          [].concat(
            str("@"),
            prReference(p.reference),
            prList(
              (x) => prPatt(spc, [lApp, new L()], x),
              p.cases1
            )
          ),
          lApp
        ];
      }
      return [
        [].concat(
          surround([].concat(
            str("@"),
            prReference(p.reference),
            prList(
              (x) => prPatt(spc, [lApp, new L()], x),
              p.cases1
            )
          )),
          prList(
            (x) => prPatt(spc, [lApp, new L()], x),
            p.cases2
          )
        ),
        lApp
      ];
    } else if (p instanceof CPatAtom) {
      let r = p.reference;
      return r.caseOf<PpResult>({
        nothing: () => [str("_"), lAtom],
        just: (r) => [prReference(r), lAtom],
      });
      //} else if (p instanceof CPatOr) {
      // TODO
      //} else if (p instanceof CPatNotation) {
      // TODO
    } else if (p instanceof CPatPrim) {
      return [prPrimToken(p.token), lAtom];
    } else if (p instanceof CPatDelimiters) {
      return [
        prDelimiters(p.string, prPatt(mt, lSimplePatt, p.cases)),
        1
      ];
    } else {
      throw MatchFailure("prPatt > match", p);
    }
  }

  let [strm, prec]: [PpCmds, number] = match(p);
  let loc = casesPatternExprLoc(p);
  return prWithComments(loc, [].concat(
    sep(),
    precLess(prec, inh) ? strm : surround(strm)
  ));
}

function prAsin(
  pr: (_1: PrecAssoc, _2: ConstrExpr.ConstrExpr) => PpCmds,
  [na, indnalopt]
): PpCmds {
  let prefix = na.caseOf({
    nothing: () => mt(),
    just: (na) => [].concat(
      spc(),
      keyword("as"),
      spc(),
      prLName(na)
    ),
  });
  let suffix = indnalopt.caseOf({
    nothing: () => mt(),
    just: (i) => [].concat(
      spc(),
      keyword("in"),
      spc(),
      prPatt(mt, lSimplePatt, i)
    ),
  });
  return [].concat(
    prefix,
    suffix
  );
}

function prCaseItem(
  pr: (_1: PrecAssoc, _2: ConstrExpr.ConstrExpr) => PpCmds,
  [tm, asin]
): PpCmds {
  return hov(0, [].concat(
    pr([lCast, new E()], tm),
    prAsin(pr, asin)
  ));
}

function sepV(): PpCmds { return [].concat(str(","), spc()); }

function constrLoc(c: ConstrExpr.ConstrExpr): CoqLocation {
  if (c instanceof ConstrExpr.CRef) {
    let ref = c.ref;
    if (ref instanceof Reference.Ident) {
      return ref.id[0];
    }
    if (ref instanceof Reference.Qualid) {
      return ref.lQualid[0];
    }
    throw MatchFailure("constrLoc", ref);
  }
  //if (c instanceof CFix) { return c.location; }
  //if (c instanceof CCoFix) { return c.location; }
  if (c instanceof ConstrExpr.CProdN) { return c.location; }
  if (c instanceof ConstrExpr.CLambdaN) { return c.location; }
  if (c instanceof ConstrExpr.CLetIn) { return c.location; }
  //if (c instanceof CAppExpl) { return c.location; }
  if (c instanceof ConstrExpr.CApp) { return c.location; }
  //if (c instanceof CRecord) { return c.location; }
  if (c instanceof ConstrExpr.CCases) { return c.location; }
  if (c instanceof ConstrExpr.CLetTuple) { return c.location; }
  //if (c instanceof CIf) { return c.location; }
  if (c instanceof ConstrExpr.CHole) { return c.location; }
  //if (c instanceof CPatVar) { return c.location; }
  //if (c instanceof CEvar) { return c.location; }
  if (c instanceof ConstrExpr.CSort) { return c.location; }
  //if (c instanceof CCast) { return c.location; }
  if (c instanceof ConstrExpr.CNotation) { return c.location; }
  //if (c instanceof CGeneralization) { return c.location; }
  if (c instanceof ConstrExpr.CPrim) { return c.location; }
  if (c instanceof ConstrExpr.CDelimiters) { return c.location; }
  throw MatchFailure("constrLoc", c);
}

function prSepCom(sep, f, c): PpCmds {
  return prWithComments(constrLoc(c), [].concat(sep(), f(c)));
}

function prCaseType(
  pr: (_1: PrecAssoc, _2: ConstrExpr.ConstrExpr) => PpCmds,
  po: Maybe<ConstrExpr.ConstrExpr>
): PpCmds {
  // TODO: po instanceof CHole with IntroAnonymous
  return po.caseOf({
    nothing: () => mt(),
    just: (po) => [].concat(
      spc(),
      hov(2, [].concat(
        keyword("return"),
        prSepCom(spc, (x) => pr(lSimpleConstr, x), po)
      ))
    ),
  });
}

function prBar() { return [].concat(str(";"), spc()); }

function prEqn(
  pr: (_1: PrecAssoc, _2: ConstrExpr.ConstrExpr) => PpCmds,
  [loc, pl0, rhs]: ConstrExpr.BranchExpr
): PpCmds {
  let pl1 = _(pl0).map((located: Located<Array<CasesPatternExpr>>) => located[1]).value();
  return [].concat(
    spc(),
    hov(4,
      prWithComments(
        loc,
        [].concat(
          str("| "),
          hov(0, [].concat(
            prListWithSep(
              prBar,
              (x) => prListWithSep(sepV, (y) => prPatt(mt, lTop, y), x),
              pl1
            ),
            str(" =>")
          )),
          prSepCom(spc, (x) => pr(lTop, x), rhs)
        )
      )
    )
  );
}

function prSimpleReturnType(
  pr: (_1: PrecAssoc, _2: ConstrExpr.ConstrExpr) => PpCmds,
  na: Maybe<Located<NameBase.Name>>,
  po: Maybe<ConstrExpr.ConstrExpr>
): PpCmds {
  let res = [];

  na.caseOf({
    nothing: () => { res = res.concat(mt()); },
    just: (na) => {
      let name = na.some[1];
      if (name instanceof NameBase.Name) {
        res = res.concat(spc(), keyword("as"), spc(), prId(name.id));
      } else {
        res = res.concat(mt);
      }
    },
  });

  res = res.concat(prCaseType(pr, po));

  return res;
}

function extractLamBinders(a: ConstrExpr.ConstrExpr): [LocalBinder.LocalBinder[], ConstrExpr.ConstrExpr] {
  if (a instanceof ConstrExpr.CLambdaN) {
    if (a.binders.length === 0) {
      return extractLamBinders(a.body);
    } else {
      let [nal, bk, t] = a.binders[0];
      let [bl, c] = extractLamBinders(a.body);
      let res: LocalBinder.LocalBinder[] = [new LocalBinder.LocalRawAssum(nal, bk, t)]
      return [res.concat(bl), c];
    }
  } else {
    return [[], a];
  }
}

let prFunSep: PpCmds = [].concat(spc(), str("=>"));

function prGen(
  pr: (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr.ConstrExpr) => PpCmds
): (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr.ConstrExpr) => PpCmds {
  return function(
    sep: () => PpCmds,
    inherited: PrecAssoc,
    a: ConstrExpr.ConstrExpr
  ): PpCmds {

    function ret(cmds: PpCmds, prec: number): PpResult {
      return [tagConstrExpr(a, cmds), prec];
    }

    let prmt = (x, y) => pr(mt, x, y);

    function match(a: ConstrExpr.ConstrExpr): PpResult {

      if (a instanceof ConstrExpr.CApp) {
        // TODO: ldots_var
        let pf = a.function[0];
        let f = a.function[1];
        return pf.caseOf<PpResult>({
          nothing: () => {
            let b = <ConstrExpr.CApp>a; // TS bug
            let [f, l] = [b.function[1], b.arguments];
            return ret(prApp(prmt, f, l), lApp);
          },
          just: (pf) => {
            let b = <ConstrExpr.CApp>a; // TS bug
            let [i, f, l] = [pf, b.function[1], b.arguments];
            let [l1, l2] = chop(i, l);
            let [c, rest] = sepLast(l1);
            // TODO: assert c[1] is empty option?
            let p = prProj(prmt, prApp, c[0], f, rest);
            // TODO: it might be nice if we could highlight the structure
            // nested applications, rather than having a flat n-ary one
            if (l2.length > 0) {
              return ret(
                [].concat(
                  p,
                  prList(
                    (a) => {
                      return [].concat(spc(), prExplArgs(prmt, a));
                    },
                    l2
                  )
                ),
                lApp
              );
            } else {
              return [p, lProj];
            }
          },
        });
      }

      if (a instanceof ConstrExpr.CCases) {
        if (a.caseStyle instanceof CaseStyle.LetPatternStyle) {
          throw "TODO: LetPatternStyle";
        }
        let prDangling = (pa, c) => prDanglingWithFor(mt, pr, pa, c);
        return ret(
          v(0, hv(0, [].concat(
            keyword("match"),
            brk(1, 2),
            hov(0,
              prListWithSep(
                sepV,
                (x) => prCaseItem(prDangling, x),
                a.cases
              )
            ),
            prCaseType(prDangling, a.returnType),
            spc(),
            keyword("with"),
            prList(
              (e: ConstrExpr.BranchExpr) => prEqn((x, y) => pr(mt, x, y), e),
              a.branches
            ),
            spc(),
            keyword("end")
          ))),
          lAtom
        );
      }

      if (a instanceof ConstrExpr.CDelimiters) {
        let [sc, e] = [a.string, a.expr];
        return ret(
          prDelimiters(sc, pr(mt, [lDelim, new E()], e)),
          lDelim
        );
      }

      if (a instanceof ConstrExpr.CLambdaN) {
        let [bl, a1] = extractLamBinders(a);
        return ret(
          hov(0, [].concat(
            hov(2, prDelimitedBinders(prFun, spc, (x) => pr(spc, lTop, x), bl)),
            prFunSep,
            pr(spc, lTop, a1)
          )),
          lLambda
        );
      }

      if (a instanceof ConstrExpr.CLetIn) {
        let bound = a.bound;
        if (bound instanceof ConstrExpr.CFix || bound instanceof ConstrExpr.CCoFix) {
          throw ("TODO: pr CLetIn with CFix/CcoFix");
        }
        return ret(
          hv(0, [].concat(
            hov(2, [].concat(
              keyword("let"), spc(), prLName(a.name), str(" :="),
              pr(spc, lTop, a.bound), spc(), keyword("in")
            )),
            pr(spc, lTop, a.body)
          )),
          lLetIn
        );
      }

      if (a instanceof ConstrExpr.CLetTuple) {
        return ret(
          hv(0, [].concat(
            keyword("let"),
            spc(),
            hov(0, [].concat(
              str("("),
              prListWithSep(sepV, prLName, a.names),
              str(")"),
              prSimpleReturnType(prmt, a.returnType[0], a.returnType[1]),
              str(" :="),
              pr(spc, lTop, a.bound),
              spc(),
              keyword("in")
            )),
            pr(spc, lTop, a.body)
          )),
          lLetIn
        );
      }

      if (a instanceof ConstrExpr.CNotation) {
        if (a.notation === "(\u00A0_\u00A0)") {
          let [[t], [], []] = a.substitution;
          return ret(
            [].concat(
              pr(
                () => { return str("("); },
                [maxInt, new L()],
                t
              ),
              str(")")
            ),
            lAtom
          );
        } else {
          let [s, env] = [a.notation, a.substitution];
          return prNotation(
            (x, y) => pr(mt, x, y),
            (x, y, z) => prBindersGen((x) => pr(mt, lTop, x), x, y, z),
            s,
            env,
            a.unparsing,
            a.precedence
          );
        }
      }

      if (a instanceof ConstrExpr.CPrim) {
        return ret(
          prPrimToken(a.token),
          precOfPrimToken(a.token)
        );
      }

      if (a instanceof ConstrExpr.CProdN) {
        let [bl, aRest] = ConstrExpr.extractProdBinders(a);
        return ret(
          [].concat(
            prDelimitedBinders(
              prForall,
              spc,
              (x) => pr(mt, lTop, x),
              bl),
            str(","),
            pr(spc, lTop, aRest)
          ),
          lProd
        );
      }

      if (a instanceof ConstrExpr.CRef) {
        let [r, us] = [a.ref, a.universeInstance];
        return ret(
          prCRef(r, us),
          lAtom
        );
      }

      if (a instanceof ConstrExpr.CSort) {
        return ret(prGlobSort(a.globSort), lAtom);
      }

      throw MatchFailure("pr > match", a);

    }

    let [strm, prec] = match(a);

    let result = sep();
    if (precLess(prec, inherited)) {
      result = result.concat(strm);
    } else {
      result = result.concat(surround(strm));
    }
    return result;

  }
}

function fix(f) {
  return function(...x) {
    return f(fix(f))(...x);
  }
};

function prConstrExpr(a: ConstrExpr.ConstrExpr): PpCmds {
  return fix(prGen)(mt, lTop, a);
}

function prHTMLGen(
  pr: (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr.ConstrExpr) => PpCmds
): (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr.ConstrExpr) => PpCmds {
  let recur = prGen(pr);
  return function(sep: () => PpCmds, pa: PrecAssoc, e: ConstrExpr.ConstrExpr): PpCmds {
    return [].concat(
      str('<span class="ace_editor syntax">'),
      recur(sep, pa, e),
      str("</span>")
    );
  }
}

function prHTML(a: ConstrExpr.ConstrExpr): PpCmds {
  return fix(prHTMLGen)(mt, lTop, a);
}

function dumbPrintPpCmd(p: PpCmd): string {
  if (p instanceof PpCmd.PpCmdPrint) {
    return dumbPrintStrToken(p.token);
  }
  if (p instanceof PpCmd.PpCmdBox) {
    // FIXME: use blockType
    return dumbPrintPpCmds(p.contents);
  }
  if (p instanceof PpCmd.PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmd.PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmd.PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmd.PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmd.PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmd.PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmd.PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmd.PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmd.PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmd.PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmd.PpCmdOpenTag) {
    return "";
  }
  if (p instanceof PpCmd.PpCmdCloseTag) {
    return "";
  }
  throw MatchFailure("dumbPrintPpCmd", p);
}

function dumbPrintStrToken(t: StrToken.StrToken): string {
  if (t instanceof StrToken.StrDef) {
    return t.string;
  }
  if (t instanceof StrToken.StrLen) {
    return t.string;
  }
  throw MatchFailure("dumbPrintStrToken", t);
}

function dumbPrintPpCmds(l: PpCmds): string {
  return _.reduce(
    l,
    (acc: string, p: PpCmd) => { return acc + dumbPrintPpCmd(p); },
    ""
  );
}

function htmlPrintStrToken(t: StrToken.StrToken): string {
  if (t instanceof StrToken.StrDef) {
    return (t.string);
  }
  if (t instanceof StrToken.StrLen) {
    return (t.string);
  }
  throw MatchFailure("htmlPrintStrToken", t);
}

function htmlPrintPpCmd(p: PpCmd): string {
  if (p instanceof PpCmd.PpCmdPrint) {
    return htmlPrintStrToken(p.token);
  }
  if (p instanceof PpCmd.PpCmdBox) {
    // FIXME: use blockType
    return syntax(htmlPrintPpCmds(p.contents));
  }
  if (p instanceof PpCmd.PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmd.PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmd.PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmd.PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmd.PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmd.PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmd.PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmd.PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmd.PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmd.PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmd.PpCmdOpenTag) {
    return "<span class=tag-" + p.tag + ">";
  }
  if (p instanceof PpCmd.PpCmdCloseTag) {
    return "</span>";
  }
  throw MatchFailure("htmlPrintPpCmd", p);
}

function htmlPrintPpCmds(l: PpCmds): string {
  _(patterns).each(function(pattern) {
    l = pattern(l);
  });
  return _.reduce(
    l,
    (acc: string, p: PpCmd) => { return acc + htmlPrintPpCmd(p); },
    ""
  );
}

function markDifferent(s: string): string {
  return '<span class="syntax peacoq-diff">' + s + '</span>';
}

function htmlPrintPpCmdDiff(p: PpCmd, old: PpCmd): string {
  if (p.constructor !== old.constructor) {
    return markDifferent(htmlPrintPpCmd(p));
  }
  if (p instanceof PpCmd.PpCmdPrint && old instanceof PpCmd.PpCmdPrint) {
    let res = htmlPrintStrToken(p.token);
    if (p.token.string !== old.token.string) { res = markDifferent(res); }
    return res;
  }
  if (p instanceof PpCmd.PpCmdBox && old instanceof PpCmd.PpCmdBox) {
    // FIXME: use blockType
    return syntax(htmlPrintPpCmdsDiff(p.contents, old.contents));
  }
  if (p instanceof PpCmd.PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmd.PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmd.PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmd.PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmd.PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmd.PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmd.PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmd.PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmd.PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmd.PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmd.PpCmdOpenTag) {
    return "<span class=tag-" + p.tag + ">";
  }
  if (p instanceof PpCmd.PpCmdCloseTag) {
    return "</span>";
  }
  throw MatchFailure("htmlPrintPpCmd", p);
}

function ppCmdSameShape(p: PpCmd, old: PpCmd): boolean {
  return (p.constructor === old.constructor);
}

function ppCmdsSameShape(l: PpCmds, old: PpCmds): boolean {
  if (l.length === 0 && old.length === 0) { return true; }
  if (l.length > 0 && old.length > 0) {
    return (
      ppCmdSameShape(l[0], old[0])
      && ppCmdsSameShape(l.slice(1), old.slice(1))
    );
  }
  return false;
}

function htmlPrintPpCmdsDiff(l: PpCmds, old: PpCmds): string {
  _(patterns).each(function(pattern) {
    l = pattern(l);
    old = pattern(old);
  });
  if (!ppCmdsSameShape(l, old)) {
    return markDifferent(
      _.reduce(
        l,
        (acc: string, p: PpCmd) => {
          return acc + htmlPrintPpCmd(p);
        },
        ""
      )
    );
  }
  var z = _.zip(l, old);
  return _.reduce(
    z,
    (acc: string, [p, oldP]: [PpCmd, PpCmd]) => {
      return acc + htmlPrintPpCmdDiff(p, oldP);
    },
    ""
  );
}
