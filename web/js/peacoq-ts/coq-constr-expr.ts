type Notation = string;

class ConstrExpr { }

type BinderExpr =[
  Array<Located<NameBase>>,
  BinderKind,
  ConstrExpr
];

type ConstrNotationSubstitution =[
  Array<ConstrExpr>,
  Array<Array<ConstrExpr>>,
  Array<Array<LocalBinder>>
];

type ProjFlag = Maybe<number>;

class Explicitation { }

class ExplByPos extends Explicitation {
  number: number;
  name: Maybe<string>;
  constructor(n: number, id: Maybe<string>) {
    super();
    this.number = n;
    this.name = id;
  }
}

class ExplByName extends Explicitation {
  name: string;
  constructor(id: string) {
    super();
    this.name = id;
  }
}

type AppFun =[ProjFlag, ConstrExpr];
type AppArg =[ConstrExpr, Maybe<Located<Explicitation>>];
type AppArgs = AppArg[];

class CApp extends ConstrExpr {
  location: Location;
  function: AppFun;
  arguments: AppArgs;
  constructor(loc: Location, f, args) {
    super();
    this.location = loc;
    this.function = f;
    this.arguments = args;
  }
}

type CaseExpr =[
  ConstrExpr,
  [Maybe<Located<Name>>, Maybe<CasesPatternExpr>]
];

type BranchExpr =[
  Location,
  Array<Located<Array<CasesPatternExpr>>>,
  ConstrExpr
];

class CCases extends ConstrExpr {
  location: Location;
  caseStyle: CaseStyle;
  constrExpr: Maybe<ConstrExpr>;
  cases: CaseExpr[];
  branches: BranchExpr[];
  constructor(loc, style, ceo, casel, branchl) {
    super();
    this.location = loc;
    this.caseStyle = style;
    this.constrExpr = ceo;
    this.cases = casel;
    this.branches = branchl;
  }
}

class CHole extends ConstrExpr {
  location: Location;
  // evarKinds
  // introPatternNamingExpr
  // rawGenericArgument
  constructor(loc: Location, eko, ipne, rgao) {
    super();
    this.location = loc;
  }
}

class CNotation extends ConstrExpr {
  location: Location;
  notation: Notation;
  substitution: ConstrNotationSubstitution;
  precedence: number;
  unparsing: Array<Unparsing>;
  constructor(
    l: Location, n: Notation, cns: ConstrNotationSubstitution,
    prec: number, unpl: Array<Unparsing>
    ) {
    super();
    this.location = l;
    this.notation = n;
    this.substitution = cns;
    this.precedence = prec;
    this.unparsing = unpl;
  }
}

class CProdN extends ConstrExpr {
  location: Location;
  binderList: Array<BinderExpr>;
  returnExpr: ConstrExpr;
  constructor(l: Location, bel: Array<BinderExpr>, ce: ConstrExpr) {
    super();
    this.location = l;
    this.binderList = bel;
    this.returnExpr = ce;
  }
}

class CPrim extends ConstrExpr {
  location: Location;
  token: PrimToken;
  constructor(l: Location, pt: PrimToken) {
    super();
    this.location = l;
    this.token = pt;
  }
}

class CRef extends ConstrExpr {
  ref: Reference;
  universeInstance: Maybe<InstanceExpr>;
  constructor(r: Reference, i: Maybe<InstanceExpr>) {
    super();
    this.ref = r;
    this.universeInstance = i;
  }
}

/***** Pretty-printing *****/

var lAtom = 0;
var lProd = 200;
var lLambda = 200;
var lIf = 200;
var lLetIn = 200;
var lLetPattern = 200;
var lFix = 200;
var lCast = 100;
var lArg = 9;
var lApp = 10;
var lPosInt = 0;
var lNegInt = 35;
var lTop: PrecAssoc = [200, new E()];
var lProj = 1;
var lDelim = 1;
var lSimpleConstr: PrecAssoc = [8, new E()];
var lSimplePatt: PrecAssoc = [1, new E()];

function precLess(child: number, parent: PrecAssoc) {
  var [parentPrec, parentAssoc] = parent;
  if (parentPrec < 0 && child === lProd) {
    return true;
  }
  parentPrec = Math.abs(parentPrec);
  if (parentAssoc instanceof E) { return child <= parentPrec; }
  if (parentAssoc instanceof L) { return child < parentPrec; }
  if (parentAssoc instanceof Prec) { return child <= parentAssoc.precedence; }
  if (parentAssoc instanceof Any) { return true; }
}

type PpResult =[string, number];

function extractProdBinders(a: ConstrExpr): [Array<LocalBinder>, ConstrExpr] {
  if (a instanceof CProdN) {
    var [loc, bl, c] = [a.location, a.binderList, a.returnExpr];
    if (bl.length === 0) {
      return extractProdBinders(a.returnExpr);
    } else {
      var [nal, bk, t] = bl[0];
      var [blrec, c] = extractProdBinders(new CProdN(loc, _.rest(bl), c));
      var l: LocalBinder[] = [new LocalRawAssum(nal, bk, t)];
      return [l.concat(blrec), c];
    }
  }
  return [[], a];
}

function MatchFailure(fn: string, o: Object) {
  if (!o) { return "undefined discriminee"; }
  return ("Match failed in " + fn + ", constructor: " + o.constructor.toString());
}

function mt() { return ""; }
function spc() { return "\u00A0"; }

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

function prComAt(n: number) { return mt(); }

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

function prLName([l, n]) {
  if (n instanceof Name) {
    return prLIdent([l, n.id]);
  } else {
    return prLocated(prName, [l, n]);
  }
}

function surroundImpl(k, p) {
  if (k instanceof Explicit) { return str("(") + p + str(")"); }
  if (k instanceof Implicit) { return str("{") + p + str("}"); }
  throw MatchFailure("surroundImpl", k);
}

function surroundImplicit(k, p) {
  if (k instanceof Explicit) { return p; }
  if (k instanceof Implicit) { return str("{") + p + str("}"); }
  throw MatchFailure("surroundImplicit", k);
}

function prBinder(many: boolean, pr: (c: ConstrExpr) => string, [nal, k, t]) {
  if (k instanceof Generalized) {
    var [b, bp, tp] = [k.kind1, k.kind2, k.b];
    return "TODO: prBinder Generalized";
  }
  if (k instanceof Default) {
    var b = k.kind;
    if (t instanceof CHole) {
      return "TODO: prBinder CHole";
    } else {
      var s = prListWithSep(spc, prLName, nal) + str("\u00A0:\u00A0") + pr(t);
      if (many) {
        return surroundImpl(b, s);
      } else {
        return surroundImplicit(b, s);
      }
    }
  }
  throw MatchFailure("prBinder", k);
}

function prDelimitedBinders(
  kw: () => string, sep: () => string, prC: (t: ConstrExpr) => string,
  bl: LocalBinder[]
  ) {
  var n = beginOfBinders(bl);
  if (bl.length === 0) { throw "prDelimitedBinders: bl should not be empty"; }
  var bl0 = bl[0];
  if (bl0 instanceof LocalRawAssum) {
    if (bl.length === 1) {
      var [nal, k, t] = [bl0.names, bl0.binderKind, bl0.term];
      return (prComAt(n) + kw() + prBinder(false, prC, [nal, k, t]));
    } else {
      return (prComAt(n) + kw() + prUndelimitedBinders(sep, prC, bl));
    }
  } else {
    throw "prDelimitedBinders: bl should only contain LocalRawAssum";
  }
}

function keyword(s) { return s; }

function prForall() {
  return keyword("forall") + spc();
}

var maxInt = 9007199254740991;

function str(s: string): string { return (s); }

function isMt(s) {
  return s === "";
}

function prListSepLastSep(noEmpty, sep, lastSep, elem, l) {
  function start(l) {
    if (l.length === 0) {
      return mt();
    } else if (length === 1) {
      return elem(l[0]);
    } else {
      var [h, t] = [l[0], _.rest(l)];
      var e = elem(h);
      if (noEmpty && isMt(e)) {
        return start(t);
      } else {
        function aux(l) {
          if (l.length === 0) {
            return mt();
          } else {
            var [h, t] = [l[0], _.rest(l)];
            var e = elem(h);
            var r = aux(t);
            if (noEmpty && isMt(e)) {
              return r;
            } else {
              if (isMt(r)) {
                return lastSep() + e;
              } else {
                return sep() + e + r;
              }
            }
          }
        }
        return e + aux(t);
      }
    }
  }
  return start(l);
}

function prListWithSep(sep, pr, l) {
  return prListSepLastSep(false, sep, sep, pr, l);
}

function prBinderAmongMany(prC, b) {
  if (b instanceof LocalRawAssum) {
    var [nal, k, t] = [b.names, b.binderKind, b.term];
    return prBinder(true, prC, [nal, k, t]);
  }
  if (b instanceof LocalRawDef) {
    var [na, c] = [b.binderName, b.binderType];
    var cp, topt;
    if (true) {//c instanceof CCast) {
      throw "TODO: prBinderAmongMany then";
    } else {
      throw "TODO: prBinderAmongMany else"
    }
    return "TODO: prBinderAmongMany";
  }
}

function prUndelimitedBinders(sep, prC, l) {
  return prListWithSep(sep, (b) => prBinderAmongMany(prC, b), l);
}

function prBindersGen(
  prC,
  sep: () => PpCmd,
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
  pr: (_1: [Notation, PrecAssoc], _2: ConstrExpr) => string,
  prBinders,
  [terms, termlists, binders]: ConstrNotationSubstitution,
  unps): string {
  var env = terms.slice(0);
  var envlist = termlists.slice(0);
  var bll = binders.slice(0);
  function pop(a: ConstrExpr[]): ConstrExpr { return a.shift(); }
  function ret(unp, pp1, pp2) { return tagUnparsing(unp, pp1) + pp2; }
  function aux(ul) {
    var pp1: string;
    var pp2: string;
    if (ul.length === 0) {
      return mt();
    }
    var unp = ul[0];
    var l = _.rest(ul);
    if (unp instanceof UnpMetaVar) {
      var prec = unp.parenRelation;
      var c = pop(env);
      pp2 = aux(l);
      pp1 = pr([n, prec], c);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpListMetaVar) {
      var [prec, sl] = [unp.parenRelation, unp.unparsing];
      var cl = pop(envlist);
      pp1 = prListWithSep(
        () => aux(sl),
        (x) => pr([n, prec], x),
        cl
        );
      pp2 = aux(l);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpBinderListMetaVar) {
      var [isOpen, sl] = [unp.isOpen, unp.unparsing];
      var cl = pop(bll);
      pp2 = aux(l);
      pp1 = prBinders(() => aux(sl), isOpen, cl);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpTerminal) {
      var s = unp.terminal;
      var pp2 = aux(l);
      var pp1 = str(s);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpBox) {
      var [b, sub] = [unp.box, unp.unparsing];
      var pp1: string = PpCmdOfBox(b, aux(sub));
      var pp2 = aux(l);
      return ret(unp, pp1, pp2);
    }
    if (unp instanceof UnpCut) {
      var pp2 = aux(l);
      var pp1 = PpCmdOfCut(unp.cut);
      return ret(unp, pp1, pp2);
    }
    throw MatchFailure("printHunks", unp);
  }
  return aux(unps);
}

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

function reprQualid(sp) { return sp; }

function tagRef(r) {
  // TODO: tag?
  return (r);
}

function tagPath(p) {
  //TODO: tag?
  return p;
}

function prList<T>(pr: (t: T) => PpCmd, l: T[]): PpCmd {
  return _.reduce(l, (acc, elt) => acc + pr(elt), mt());
}

function prQualid(sp) {
  var [sl0, id0] = reprQualid(sp);
  var id = tagRef(str(id0));
  var rev = sl0.slice(0).reverse();
  var sl;
  if (rev.length === 0) {
    sl = mt();
  } else {
    sl = prList(
      (dir: string) => tagPath(str(dir)) + str("."),
      sl0
      );
  }
  return sl + id;
}

function tagVar(v) {
  // TODO: tag?
  return v;
}

function prReference(r: Reference) {
  if (r instanceof Qualid) { return prQualid(r.lQualid[1]); }
  if (r instanceof Ident) { return tagVar(str(r.id[1])); }
  throw MatchFailure("prReference", r);
}

function tagType(t) {
  // TODO: tag?
  return t;
}

function prGlobSortInstance(i) {
  if (i instanceof GProp) { return tagType(str("Prop")); }
  if (i instanceof GSet) { return tagType(str("Set")); }
  if (i instanceof GType) {
    var t = i.type;
    if (t instanceof Some) { return str(t.some); }
    if (t instanceof None) { return tagType(str("Type")); }
    throw MatchFailure("prGlobSortInstance", t);
  }
  throw MatchFailure("prGlobSortInstance", i);
}

function prOptNoSpc(pr, x) {
  if (x instanceof None) { return mt(); }
  if (x instanceof Some) { return pr(x); }
  throw MatchFailure("prOptNoSpc", x);
}

function prUnivAnnot(pr, x) {
  return str("@{") + pr(x) + str("}");
}

function prUniverseInstance(l) {
  return prOptNoSpc(
    (x) => { prUnivAnnot((x) => prListWithSep(spc, prGlobSortInstance, x), x) },
    l
    );
}

function prCRef(r, us) {
  return prReference(r) + prUniverseInstance(us);
}

function chop<T>(i: number, l: T[]): [T[], T[]] {
  return [l.slice(0, i), l.slice(i)];
}

function sepLast<T>(l: T[]): [T, T[]] {
  var len = l.length;
  return [l[len - 1], l.slice(0, len - 1)];
}

function cut() { return ""; }

function prProj(pr, prApp, a, f, l) {
  return (
    pr([lProj, new E()], a) + cut() + str(".(") + prApp(pr, f, l) + str(")")
    );
}

type PpCmd = string;

function prExplArgs(
  pr: (pa: PrecAssoc, ce: ConstrExpr) => PpCmd,
  [a, expl]: AppArg
  ): PpCmd {
  if (expl instanceof None) {
    return pr([lApp, new L()], a);
  }
  if (expl instanceof Some) {
    var e = expl.some[1];
    if (e instanceof ExplByPos) {
      throw "Anomaly: Explicitation by position not implemented";
    }
    if (e instanceof ExplByName) {
      return (
        str("(") + prId(e.name) + str(":=") + pr(lTop, a) + str(")")
        );
    }
    throw MatchFailure("prExplArgs", e);
  }
  throw MatchFailure("prExplArgs", expl);
}

function prApp(
  pr: (_1: PrecAssoc, _2: ConstrExpr) => PpCmd,
  a: ConstrExpr,
  l: AppArgs
  ) {
  return (
    pr([lApp, new L()], a)
    + prList((x) => { return spc() + prExplArgs(pr, x); }, l)
    );
}

function precOfPrimToken(t: PrimToken): number {
  if (t instanceof Numeral) {
    if (t.numeral >= 0) { return lPosInt; } else { return lNegInt; }
  }
  if (t instanceof CoqString) {
    return lAtom;
  }
  throw MatchFailure("precOfPrimToken", t);
}

function qs(s: string): PpCmd {
  return str("\"" + s + "\"");
}

function prPrimToken(t: PrimToken): PpCmd {
  if (t instanceof Numeral) {
    return str(t.numeral.toString());
  }
  if (t instanceof CoqString) {
    return qs(t.string);
  }
  throw MatchFailure("prPrimToken", t);
}

function pr(pr): (sep: string, inherited: PrecAssoc, a: ConstrExpr) => string {
  return function(sep, inherited, a): string {

    function match(a: ConstrExpr): PpResult {

      if (a instanceof CApp) {
        // TODO: ldots_var
        var pf = a.function[0];
        var prmt = (x, y) => pr(mt, x, y);
        if (pf instanceof Some) {
          var [i, f, l] = [pf.some, a.function[1], a.arguments];
          var [l1, l2] = chop(i, l);
          var [c, l1] = sepLast(l1);
          // TODO: assert c[1] is empty option?
          var p = prProj(prmt, prApp, c[0], f, l1);
          if (l2.length > 0) {
            return [
              p + prList((a) => { return spc() + prExplArgs(prmt, a); }, l2),
              lApp
            ];
          } else {
            return [p, lProj];
          }
        }
        if (pf instanceof None) {
          var [a, l] = [a.function[1], a.arguments];
          return [prApp(prmt, a, l), lApp];
        }
        throw MatchFailure("pr -> match -> CApp", pf);
      }

      if (a instanceof CNotation) {
        if (a.notation === "( _ )") {
          var [[t], [], []] = a.substitution;
          return [
            pr(
              () => { return str("("); },
              [maxInt, new L()],
              t
              ) + str(")"),
            lAtom
          ];
        } else {
          var [s, env] = [a.notation, a.substitution];
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
        return [
          prPrimToken(a.token),
          precOfPrimToken(a.token)
        ];
      }

      if (a instanceof CProdN) {
        var [bl, a] = extractProdBinders(a);
        return [
          prDelimitedBinders(
            prForall,
            spc,
            (x) => pr(mt, lTop, x),
            bl)
          + str(",") + pr(spc, lTop, a),
          lProd
        ];
      }

      if (a instanceof CRef) {
        var [r, us] = [a.ref, a.universeInstance];
        return [
          prCRef(r, us),
          lAtom
        ]
      }

      throw MatchFailure("pr", a);

    }

    var [string, prec] = match(a);

    var result = spc();
    if (precLess(prec, inherited)) {
      result += string;
    } else {
      result += "(" + string + ")";
    }
    return result;

  }
}

function fix(f) {
  return function(...x) {
    return f(fix(f))(...x);
  }
};

function prettyPrint(a: ConstrExpr): string {
  return fix(pr)(mt, lTop, a);
}
