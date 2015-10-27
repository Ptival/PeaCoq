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

type PpResult =[PpCmds, number];

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

function MatchFailure(fn: string, o: Object) {
  if (!o) { return "undefined discriminee"; }
  return ("Match failed in " + fn + ", constructor: " + o.constructor.toString());
}

function MissingOverload(fn: string, o: Object) {
  return ("Missing overload " + fn + ", constructor: " + o.constructor.toString());
}

function cut(): PpCmds { return [new PpCmdPrintBreak(0, 0)]; }
function mt(): PpCmds { return []; }
function spc(): PpCmds { return [new PpCmdPrintBreak(1, 0)]; }
function str(s: string): PpCmds { return [new PpCmdPrint(new StrDef(s))]; }
function surround(p: PpCmds): PpCmds {
  return hov(1, [].concat(str("("), p, str(")")));
}

function isMt(p: PpCmds): boolean {
  return (p.length === 0);
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

function prLName([l, n]) {
  if (n instanceof Name) {
    return prLIdent([l, n.id]);
  } else {
    return prLocated(prName, [l, n]);
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
        return surroundImpl(b, s);
      } else {
        return surroundImplicit(b, s);
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

function tagKeyword(p: PpCmds): PpCmds { return p; }

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
    if (true) {//c instanceof CCast) {
      throw "TODO: prBinderAmongMany then";
    } else {
      throw "TODO: prBinderAmongMany else"
    }
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
  function ret(unp: Unparsing, pp1: PpCmds, pp2: PpCmds): PpCmds { return [].concat(tagUnparsing(unp, pp1), pp2); }
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

function tagRef(r: PpCmds): PpCmds {
  // TODO: tag?
  return (r);
}

function tagPath(p: PpCmds): PpCmds {
  //TODO: tag?
  return p;
}

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

function tagVar(v) {
  // TODO: tag?
  return v;
}

function prReference(r: Reference): PpCmds {
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
  if (t instanceof CoqString) {
    return lAtom;
  }
  throw MatchFailure("precOfPrimToken", t);
}

function qs(s: string): PpCmds { return str("\"" + s + "\""); }

function prPrimToken(t: PrimToken): PpCmds {
  if (t instanceof Numeral) {
    return str(t.numeral.toString());
  }
  if (t instanceof CoqString) {
    return qs(t.string);
  }
  throw MatchFailure("prPrimToken", t);
}

function pr(
  pr: (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr) => PpCmds
  ): (_1: () => PpCmds, _2: PrecAssoc, _3: ConstrExpr) => PpCmds {
  return function(
    sep: () => PpCmds,
    inherited: PrecAssoc,
    a: ConstrExpr
    ): PpCmds {

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
          if (l2.length > 0) {
            return [
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
            ];
          } else {
            return [p, lProj];
          }
        }
        if (pf instanceof None) {
          let [f, l] = [a.function[1], a.arguments];
          return [prApp(prmt, f, l), lApp];
        }
        throw MatchFailure("pr -> match -> CApp", pf);
      }

      if (a instanceof CNotation) {
        if (a.notation === "( _ )") {
          let [[t], [], []] = a.substitution;
          return [
            [].concat(
              pr(
                () => { return str("("); },
                [maxInt, new L()],
                t
                ),
              str(")")
              ),
            lAtom
          ];
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
        return [
          prPrimToken(a.token),
          precOfPrimToken(a.token)
        ];
      }

      if (a instanceof CProdN) {
        let [bl, aRest] = extractProdBinders(a);
        return [
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
        ];
      }

      if (a instanceof CRef) {
        let [r, us] = [a.ref, a.universeInstance];
        return [
          prCRef(r, us),
          lAtom
        ]
      }

      throw MatchFailure("pr", a);

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
  return fix(pr)(mt, lTop, a);
}
