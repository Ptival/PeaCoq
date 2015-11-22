class StrToken { }
class StrDef extends StrToken {
  string: string;
  constructor(s: string) {
    super();
    this.string = s;
  }
}
class StrLen extends StrToken {
  string: string;
  length: number;
  constructor(s: string, l: number) {
    super();
    this.string = s;
    this.length = l;
  }
}

class PpCmdToken<T> { }

class PpCmdPrint<T> extends PpCmdToken<T> {
  token: T;
  constructor(t: T) {
    super();
    this.token = t;
  }
}

class PpCmdBox<T> extends PpCmdToken<T> {
  blockType: BlockType;
  contents: PpCmdToken<T>[];
  constructor(b: BlockType, x: PpCmdToken<T>[]) {
    super();
    this.blockType = b;
    this.contents = x;
  }
}

class PpCmdPrintBreak<T> extends PpCmdToken<T> {
  nspaces: number;
  offset: number;
  constructor(x: number, y: number) {
    super();
    this.nspaces = x;
    this.offset = y;
  }
}

class PpCmdSetTab<T> extends PpCmdToken<T> { }

class PpCmdPrintTbreak<T> extends PpCmdToken<T> {
  constructor(x: number, y: number) {
    super();
  }
}

class PpCmdWhiteSpace<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super();
  }
}

class PpCmdForceNewline<T> extends PpCmdToken<T> { }

class PpCmdPrintIfBroken<T> extends PpCmdToken<T> { }

class PpCmdOpenBox<T> extends PpCmdToken<T> {
  blockType: BlockType;
  constructor(b: BlockType) {
    this.blockType = b;
    super();
  }
}

class PpCmdCloseBox<T> extends PpCmdToken<T> { }

class PpCmdCloseTBox<T> extends PpCmdToken<T> { }

class PpCmdComment<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super();
  }
}

type Tag = string;

function tagEvar(p: PpCmds): PpCmds { return tag("evar", p); }
function tagKeyword(p: PpCmds): PpCmds { return tag("keyword", p); }
function tagNotation(r: PpCmds): PpCmds { return tag("notation", r); }
function tagPath(p: PpCmds): PpCmds { return tag("path", p); }
function tagRef(r: PpCmds): PpCmds { return tag("reference", r); }
function tagType(r: PpCmds): PpCmds { return tag("univ", r); }
function tagVariable(p: PpCmds): PpCmds { return tag("variable", p); }

class PpCmdOpenTag<T> extends PpCmdToken<T> {
  tag: string;
  constructor(t: Tag) {
    this.tag = t;
    super();
  }
}

class PpCmdCloseTag<T> extends PpCmdToken<T> { }

type PpCmd = PpCmdToken<StrToken>;
type PpCmds = PpCmd[];

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

function precLess(child: number, parent: PrecAssoc) {
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

function extractProdBinders(a: ConstrExpr): [Array<LocalBinder>, ConstrExpr] {
  if (a instanceof CProdN) {
    let [loc, bl, c] = [a.location, a.binderList, a.returnExpr];
    if (bl.length === 0) {
      return extractProdBinders(a.returnExpr);
    } else {
      let [nal, bk, t] = bl[0];
      let [blrec, cRest] = extractProdBinders(new CProdN(loc, _.rest(bl), c));
      let l: LocalBinder[] = [new LocalRawAssum(nal, bk, t)];
      return [l.concat(blrec), cRest];
    }
  }
  return [[], a];
}

function cut(): PpCmds { return [new PpCmdPrintBreak(0, 0)]; }
function mt(): PpCmds { return []; }
function spc(): PpCmds { return [new PpCmdPrintBreak(1, 0)]; }
function str(s: string): PpCmds { return [new PpCmdPrint(new StrDef(s))]; }
function surround(p: PpCmds): PpCmds {
  return hov(1, [].concat(str("("), p, str(")")));
}

function openTag(t: Tag): PpCmds { return [new PpCmdOpenTag(t)]; }
function closeTag(t: Tag): PpCmds { return [new PpCmdCloseTag()]; }
function tag(t: Tag, s: PpCmds): PpCmds {
  return [].concat(openTag(t), s, closeTag(t));
}

function isMt(p: PpCmds): boolean {
  return (p.length === 0);
}

/*
peaCoqBox should not disrupt the pretty-printing flow, but add a
<span> so that sub-expression highlighting is more accurate
*/
function peaCoqBox(l: PpCmds): PpCmds {
  return [new PpCmdBox(new PpHoVBox(0), l)];
}

function beginOfBinder(b: LocalBinder): number {
  if (b instanceof LocalRawDef) {
    return b.binderName[0][0];
  }
  if (b instanceof LocalRawAssum) {
    return b.names[0][0][0];
  }
  throw MatchFailure("beginOfBinder", b);
}

function beginOfBinders(bl) {
  if (bl.length === 0) { return 0; }
  else { return beginOfBinder(bl[0]); }
}

function prComAt(n: number): PpCmds { return mt(); }

function prId(id) { return str(id); }

function prLIdent([loc, id]) {
  // TODO: Loc.is_ghost
  return prId(id);
}

function prLocated(pr, [loc, x]) {
  // TODO: Flags.beautify?
  return pr(x);
}

function prName(n) {
  if (n instanceof Anonymous) {
    return str("_");
  }
  if (n instanceof Name) {
    return prId(n.id);
  }
  throw MatchFailure("prName", n);
}

function prLName([l, n]: [PpCmds, NameBase]): PpCmds {
  if (n instanceof Name) {
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
  pr: (c: ConstrExpr) => PpCmds,
  [nal, k, t]
  ): PpCmds {
  if (k instanceof Generalized) {
    let [b, bp, tp] = [k.kind1, k.kind2, k.b];
    throw "TODO: prBinder Generalized";
  }
  if (k instanceof Default) {
    let b = k.kind;
    if (t instanceof CHole) {
      throw "TODO: prBinder CHole";
    } else {
      let s = [].concat(
        prListWithSep(spc, prLName, nal),
        str("\u00A0:\u00A0"),
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
  prC: (t: ConstrExpr) => PpCmds,
  bl: LocalBinder[]
  ): PpCmds {
  let n = beginOfBinders(bl);
  if (bl.length === 0) { throw "prDelimitedBinders: bl should not be empty"; }
  let bl0 = bl[0];
  if (bl0 instanceof LocalRawAssum) {
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

function keyword(s: string): PpCmds { return tagKeyword(str(s)); }

function prForall(): PpCmds {
  return [].concat(keyword("forall"), spc());
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
      let [h, t] = [l[0], _.rest(l)];
      let e = elem(h);
      if (noEmpty && isMt(e)) {
        return start(t);
      } else {
        function aux(l: T[]): PpCmds {
          if (l.length === 0) {
            return mt();
          } else {
            let [h, t] = [l[0], _.rest(l)];
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

function prBinderAmongMany(prC, b): PpCmds {
  if (b instanceof LocalRawAssum) {
    let [nal, k, t] = [b.names, b.binderKind, b.term];
    return prBinder(true, prC, [nal, k, t]);
  }
  if (b instanceof LocalRawDef) {
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
  ul: LocalBinder[]
  ) {
  if (isOpen) {
    return prDelimitedBinders(mt, sep, prC, ul);
  } else {
    return prUndelimitedBinders(sep, prC, ul);
  }
}

function printHunks(
  n,
  pr: (_1: [number, ParenRelation], _2: ConstrExpr) => PpCmds,
  prBinders: (_1: () => PpCmds, _2: boolean, _3: ConstrExpr) => PpCmds,
  [terms, termlists, binders]: ConstrNotationSubstitution,
  unps: Unparsing[])
  : PpCmds {
  let env = terms.slice(0);
  let envlist = termlists.slice(0);
  let bll = binders.slice(0);
  function pop(a: ConstrExpr[]): ConstrExpr { return a.shift(); }
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
    let l = _.rest(ul);
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

type PpResult =[PpCmds, number];

// Here Coq would consult the notation table to figure [unpl] and [level] from
// [s], but we have it already figured out.
function prNotation(
  pr, prBinders, s,
  env: ConstrNotationSubstitution,
  unpl: Unparsing[],
  level: number
  ): PpResult {
  return [
    printHunks(level, pr, prBinders, env, unpl),
    level
  ];
}

function reprQualid(sp: QualId): QualId { return sp; }

function prList<T>(pr: (t: T) => PpCmds, l: T[]): PpCmds {
  return _.reduce(l, (acc, elt) => { return acc.concat(pr(elt)); }, mt());
}

function prQualid(sp: QualId): PpCmds {
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

function prReference(r: Reference): PpCmds {
  if (r instanceof Qualid) { return peaCoqBox(prQualid(r.lQualid[1])); }
  if (r instanceof Ident) { return peaCoqBox(tagVariable(str(r.id[1]))); }
  throw MatchFailure("prReference", r);
}

function prGlobSortInstance(i) {
  if (i instanceof GProp) { return tagType(str("Prop")); }
  if (i instanceof GSet) { return tagType(str("Set")); }
  if (i instanceof GType) {
    let t = i.type;
    if (t instanceof Some) { return str(t.some); }
    if (t instanceof None) { return tagType(str("Type")); }
    throw MatchFailure("prGlobSortInstance", t);
  }
  throw MatchFailure("prGlobSortInstance", i);
}

function prOptNoSpc<T>(pr: (T) => PpCmds, x: Maybe<T>): PpCmds {
  if (x instanceof None) { return mt(); }
  if (x instanceof Some) { return pr(x); }
  throw MatchFailure("prOptNoSpc", x);
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

function prCRef(r: Reference, us: Maybe<InstanceExpr>): PpCmds {
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
  pr: (_1, _2: ConstrExpr) => PpCmds,
  prApp,
  a: ConstrExpr,
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
  pr: (pa: PrecAssoc, ce: ConstrExpr) => PpCmds,
  [a, expl]: AppArg
  ): PpCmds {
  if (expl instanceof None) {
    return pr([lApp, new L()], a);
  }
  if (expl instanceof Some) {
    let e = expl.some[1];
    if (e instanceof ExplByPos) {
      throw "Anomaly: Explicitation by position not implemented";
    }
    if (e instanceof ExplByName) {
      return ([].concat(str("("), prId(e.name), str(":="), pr(lTop, a), str(")")));
    }
    throw MatchFailure("prExplArgs", e);
  }
  throw MatchFailure("prExplArgs", expl);
}

function prApp(
  pr: (_1: PrecAssoc, _2: ConstrExpr) => PpCmds,
  a: ConstrExpr,
  l: AppArgs
  ) {
  return ([].concat(
    pr([lApp, new L()], a),
    prList((x) => { return [].concat(spc(), prExplArgs(pr, x)); }, l)
    ));
}

function precOfPrimToken(t: PrimToken): number {
  if (t instanceof Numeral) {
    if (t.numeral >= 0) { return lPosInt; } else { return lNegInt; }
  }
  if (t instanceof PrimTokenString) {
    return lAtom;
  }
  throw MatchFailure("precOfPrimToken", t);
}

function qs(s: string): PpCmds { return str("\"" + s + "\""); }

function prPrimToken(t: PrimToken): PpCmds {
  if (t instanceof Numeral) {
    return str(t.numeral.toString());
  }
  if (t instanceof PrimTokenString) {
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

function tagConstrExpr(ce: ConstrExpr, cmds: PpCmds) {
  return peaCoqBox(cmds);
}

function prDanglingWithFor(
  sep: () => PpCmds,
  pr: (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr) => PpCmds,
  inherited: PrecAssoc,
  a: ConstrExpr
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
  p: ConstrExpr
  ): PpCmds {
  let match = (p: ConstrExpr): [PpCmds, number]=> {
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
  pr: (_1: PrecAssoc, _2: ConstrExpr) => PpCmds,
  [na, indnalopt]
  ): PpCmds {
  let prefix;
  if (na instanceof Some) {
    prefix = [].concat(
      spc(),
      keyword("as"),
      spc(),
      prLName(na.some)
      );
  }
  else if (na instanceof None) {
    prefix = mt();
  } else {
    throw MatchFailure("prAsin", na);
  }
  let suffix;
  if (indnalopt instanceof None) {
    suffix = mt();
  }
  else if (indnalopt instanceof Some) {
    suffix = [].concat(
      spc(),
      keyword("in"),
      spc(),
      prPatt(mt, lSimplePatt, indnalopt.some)
      );
  } else {
    throw MatchFailure("prAsin", indnalopt);
  }
  return [].concat(
    prefix,
    suffix
    );
}

function prCaseItem(
  pr: (_1: PrecAssoc, _2: ConstrExpr) => PpCmds,
  [tm, asin]
  ): PpCmds {
  return hov(0, [].concat(
    pr([lCast, new E()], tm),
    prAsin(pr, asin)
    ));
}

function sepV(): PpCmds { return [].concat(str(","), spc()); }

function constrLoc(c: ConstrExpr): CoqLocation {
  if (c instanceof CRef) {
    let ref = c.ref;
    if (ref instanceof Ident) {
      return ref.id[0];
    }
    if (ref instanceof Qualid) {
      return ref.lQualid[0];
    }
    throw MatchFailure("constrLoc", ref);
  }
  //if (c instanceof CFix) { return c.location; }
  //if (c instanceof CCoFix) { return c.location; }
  if (c instanceof CProdN) { return c.location; }
  //if (c instanceof CLambdaN) { return c.location; }
  if (c instanceof CLetIn) { return c.location; }
  //if (c instanceof CAppExpl) { return c.location; }
  if (c instanceof CApp) { return c.location; }
  //if (c instanceof CRecord) { return c.location; }
  if (c instanceof CCases) { return c.location; }
  //if (c instanceof CLetTuple) { return c.location; }
  //if (c instanceof CIf) { return c.location; }
  if (c instanceof CHole) { return c.location; }
  //if (c instanceof CPatVar) { return c.location; }
  //if (c instanceof CEvar) { return c.location; }
  if (c instanceof CSort) { return c.location; }
  //if (c instanceof CCast) { return c.location; }
  if (c instanceof CNotation) { return c.location; }
  //if (c instanceof CGeneralization) { return c.location; }
  if (c instanceof CPrim) { return c.location; }
  if (c instanceof CDelimiters) { return c.location; }
  throw MatchFailure("constrLoc", c);
}

function prSepCom(sep, f, c): PpCmds {
  return prWithComments(constrLoc(c), [].concat(sep(), f(c)));
}

function prCaseType(
  pr: (_1: PrecAssoc, _2: ConstrExpr) => PpCmds,
  po: Maybe<ConstrExpr>
  ): PpCmds {
  // TODO: po instanceof CHole with IntroAnonymous
  if (po instanceof None) { return mt(); }
  if (po instanceof Some) {
    return [].concat(
      spc(),
      hov(2, [].concat(
        keyword("return"),
        prSepCom(spc, (x) => pr(lSimpleConstr, x), po.some)
        ))
      );
  }
}

function prBar() { return [].concat(str(";"), spc()); }

function prEqn(
  pr: (_1: PrecAssoc, _2: ConstrExpr) => PpCmds,
  [loc, pl0, rhs]: BranchExpr
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

function prGen(
  pr: (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr) => PpCmds
  ): (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr) => PpCmds {
  return function(
    sep: () => PpCmds,
    inherited: PrecAssoc,
    a: ConstrExpr
    ): PpCmds {

    function ret(cmds: PpCmds, prec: number): PpResult {
      return [tagConstrExpr(a, cmds), prec];
    }

    function match(a: ConstrExpr): PpResult {

      if (a instanceof CApp) {
        // TODO: ldots_var
        let pf = a.function[0];
        let prmt = (x, y) => pr(mt, x, y);
        if (pf instanceof Some) {
          let [i, f, l] = [pf.some, a.function[1], a.arguments];
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
        }
        if (pf instanceof None) {
          let [f, l] = [a.function[1], a.arguments];
          return ret(prApp(prmt, f, l), lApp);
        }
        throw MatchFailure("pr -> match -> CApp", pf);
      }

      if (a instanceof CCases) {
        if (a.caseStyle instanceof LetPatternStyle) {
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
              (e: BranchExpr) => prEqn((x, y) => pr(mt, x, y), e),
              a.branches
              ),
            spc(),
            keyword("end")
            ))),
          lAtom
          );
      }

      if (a instanceof CDelimiters) {
        let [sc, e] = [a.string, a.expr];
        return ret(
          prDelimiters(sc, pr(mt, [lDelim, new E()], e)),
          lDelim
          );
      }

      if (a instanceof CLetIn) {
        let bound = a.bound;
        if (bound instanceof CFix || bound instanceof CCoFix) {
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

      if (a instanceof CNotation) {
        if (a.notation === "( _ )") {
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

      if (a instanceof CPrim) {
        return ret(
          prPrimToken(a.token),
          precOfPrimToken(a.token)
          );
      }

      if (a instanceof CProdN) {
        let [bl, aRest] = extractProdBinders(a);
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

      if (a instanceof CRef) {
        let [r, us] = [a.ref, a.universeInstance];
        return ret(
          prCRef(r, us),
          lAtom
          );
      }

      if (a instanceof CSort) {
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

function prConstrExpr(a: ConstrExpr): PpCmds {
  return fix(prGen)(mt, lTop, a);
}

function prHTMLGen(
  pr: (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr) => PpCmds
  ): (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr) => PpCmds {
  let recur = prGen(pr);
  return function(sep: () => PpCmds, pa: PrecAssoc, e: ConstrExpr): PpCmds {
    return [].concat(
      str('<span class="ace_editor syntax">'),
      recur(sep, pa, e),
      str("</span>")
      );
  }
}

function prHTML(a: ConstrExpr): PpCmds {
  return fix(prHTMLGen)(mt, lTop, a);
}

function dumbPrintPpCmd(p: PpCmd): string {
  if (p instanceof PpCmdPrint) {
    return dumbPrintStrToken(p.token);
  }
  if (p instanceof PpCmdBox) {
    // FIXME: use blockType
    return dumbPrintPpCmds(p.contents);
  }
  if (p instanceof PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmdOpenTag) {
    return "TODO: PpCmdOpenTag";
  }
  if (p instanceof PpCmdCloseTag) {
    return "TODO: PpCmdCloseTag";
  }
  throw MatchFailure("dumbPrintPpCmd", p);
}

function dumbPrintStrToken(t: StrToken): string {
  if (t instanceof StrDef) {
    return t.string;
  }
  if (t instanceof StrLen) {
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

function syntax(s: string): string {
  return '<span class="syntax">' + s + "</span>";
}

function htmlPrintStrToken(t: StrToken): string {
  if (t instanceof StrDef) {
    return (t.string);
  }
  if (t instanceof StrLen) {
    return (t.string);
  }
  throw MatchFailure("htmlPrintStrToken", t);
}

function htmlPrintPpCmd(p: PpCmd): string {
  if (p instanceof PpCmdPrint) {
    return htmlPrintStrToken(p.token);
  }
  if (p instanceof PpCmdBox) {
    // FIXME: use blockType
    return syntax(htmlPrintPpCmds(p.contents));
  }
  if (p instanceof PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmdOpenTag) {
    return "<span class=tag-" + p.tag + ">";
  }
  if (p instanceof PpCmdCloseTag) {
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
  if (p instanceof PpCmdPrint && old instanceof PpCmdPrint) {
    let res = htmlPrintStrToken(p.token);
    if (p.token.string !== old.token.string) { res = markDifferent(res); }
    return res;
  }
  if (p instanceof PpCmdBox && old instanceof PpCmdBox) {
    // FIXME: use blockType
    return syntax(htmlPrintPpCmdsDiff(p.contents, old.contents));
  }
  if (p instanceof PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmdOpenTag) {
    return "<span class=tag-" + p.tag + ">";
  }
  if (p instanceof PpCmdCloseTag) {
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
