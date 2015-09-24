class PrecAssoc {
  associativity: Associativity;
  precedence: number;
  constructor(prec: number, assoc: Associativity) {
    this.precedence = prec;
    this.associativity = assoc;
  }
}

class Associativity { }
class E extends Associativity { }
class L extends Associativity { }
class Prec extends Associativity {
  precedence: number;
  constructor(prec: number) {
    super();
    this.precedence = prec;
  }
}
class Any extends Associativity { }

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
var lTop = new PrecAssoc(200, new E());
var lProj = 1;
var lDelim = 1;
var lSimpleConstr = new PrecAssoc(8, new E());
var lSimplePatt = new PrecAssoc(1, new E());

type PP = (pa: PrecAssoc, a: Term) => string;

function ppListSepLastSep(noEmpty: boolean, sep: () => string, lastSep: () => string, elem: (t: Term) => string) {
  var start = function(a) {
    if (a.length === 0) { return ""; }
    else if (a.length === 1) { return elem(a[0]); }
    else {
      var e = elem(a[0]);
      var t = _.rest(a);
      if (noEmpty && e === "") {
        return start(t);
      } else {
        var aux = function(a) {
          if (a.length === 0) {
            return "";
          } else {
            var e = elem(a[0]);
            var r = aux(_.rest(a));
            if (noEmpty && e === "") {
              return r;
            } else {
              if (r === "") {
                return lastSep () + e;
              } else {
                return sep () + e + r;
              }
            }
          }
        };
        return e + aux(t);
      }
    }
  }
  return start;
}

function ppListWithSep(sep: () => string, pr: (t: Term) => string, l: Array<Term>) {
  return ppListSepLastSep(false, sep, sep, pr)(l);
}

function ppList<T>(pp: (t: T) => string, l: Array<T>): string {
  return _(l).reduce(function(acc, elt) { return acc + pp(elt); }, "");
}

function ppSepCom(sep: string, f: (pa: PrecAssoc) => string, pa: PrecAssoc) {
  return sep + f(pa);
}

function ppExplArgs(pp: PP, a: Term): string {
  // TODO: explicitation
  return pp(new PrecAssoc(lApp, new L()), a);
}

function ppQualid(qualid: Qualid): string {
  return qualid.ppQualid;
}

function ppReference(ref): string {
  if (ref instanceof Qualid) {
    return ppQualid(ref);
  }
  if (ref instanceof Ident) {
    return ref.id;
  }
  throw "ppReference";
}

function ppRef(ref: Reference): string {
  // TODO: universe instance
  return ppReference(ref);
}

function ppApp(pp: PP, a: Term, l: Array<Term>) {
  return (
    pp(new PrecAssoc(lApp, new L()), a)
    + ppList((a) => { return " " + ppExplArgs(pp, a); }, l)
    );
}

type PpResult = { string: string; precedence: number };

function ppBinderAmongMany(ppC) {
  return (c) => { "TODO" };
}

function ppUndelimitedBinders(sep, ppC) {
  //return ppListWithSep(sep, ppBinderAmongMany(ppC));
  return (c) => { "TODO" };
}

function ppDelimitedBinders(kw, sep, prC) {
  return (bl) => { "TODO" };
}

function ppBindersGen(ppC: (t: Term) => string, sep, isOpen) {
  if (isOpen) {
    return ppDelimitedBinders("", sep, ppC);
  } else {
    return ppUndelimitedBinders(sep, ppC);
  }
}

function pp(pp): (sep: string, inherited: PrecAssoc, a: Term) => string {
  return function(sep, inherited, a): string {

    function ret(s: string, p: number): PpResult {
      return {
        string: s,
        precedence: p,
      }
    }

    function match(a) {

      if (a.annotation instanceof NotationRoot) {
        var notation_Rule = a.annotation.notationRule;
        var substitutions = a.annotation.substitutions;
        var ir = notation_Rule.interpRule;

        if (ir instanceof NotationRule) {
          var level = ir.precedence;
          var ppBinders =
            _.partial(
              ppBindersGen,
              _.partial(pp, "", lTop)
              );

          return ret(
            printHunks(
              level,
              (pa, c) => pp("", pa, c),
              ppBinders,
              substitutions,
              ir.unparsing
              ),
            level);
        }

        if (ir instanceof SynDefRule) {
          var sdr = <SynDefRule>ir;
          throw "TODO: SynDefRule";
        }

        throw "match";
      }

      if (a instanceof Ref) {
        return ret(ppRef(a.reference), lAtom);
      }

      if (a instanceof App) {
        return ret(
          ppApp(
            (inherited, number) => pp("", inherited, number),
            a.function,
            a.arguments
            ),
          lApp
          );
      }

      if (a instanceof Prim) {
        var p = a.prim;
        return ret(p.pp(), p.prec());
      }

      if (a instanceof Hole) {
        return ret("_", lAtom);
      }

      throw "match failed!";
    }

    var matchResult = match(a);

    if (precLess(matchResult.precedence, inherited)) {
      return matchResult.string;
    } else {
      return "(" + matchResult.string + ")";
    }

  }
}

function fix(f) {
  return function(...x) {
    return f(fix(f))(...x);
  }
};

function prettyPrint(a: Term): string {
  return fix(pp)("", lTop, a);
}

class Term {
  annotation: Notation;
  constructor(a: Notation) {
    this.annotation = a;
  }
}

class App extends Term {
  function: Term;
  arguments: Array<Term>;
  constructor(a: Notation, t: Term, tl: Array<Term>) {
    super(a);
    this.function = t;
    this.arguments = tl;
  }
}

class Hole extends Term {
  constructor(a: Notation) {
    super(a);
  }
}

class Ref extends Term {
  baseName: string;
  globalReference: GlobalReference;
  reference: Reference;
  constructor(a: Notation, gr: GlobalReference, r: Reference, baseName: string) {
    super(a);
    this.baseName = baseName;
    this.globalReference = gr;
    this.reference = r;
  }
}

class Prim extends Term {
  prim: PrimToken;
  constructor(a: Notation, pt: PrimToken) {
    super(a);
    this.prim = pt;
  }
}

class GlobalReference { }

class VarRef extends GlobalReference {
  variable: string;
  constructor(v: string) {
    super();
    this.variable = v;
  }
}

class ConstRef extends GlobalReference {
  constant: string;
  constructor(c: string) {
    super();
    this.constant = c;
  }
}

class IndRef extends GlobalReference {
  inductive: Inductive;
  constructor(i: Inductive) {
    super();
    this.inductive = i;
  }
}

class ConstructRef extends GlobalReference {
  construct: Constructor;
  constructor(c: Constructor) {
    super();
    this.construct = c;
  }
}

class Inductive {
  index: number;
  name: string;
  constructor(name: string, index: number) {
    this.name = name;
    this.index = index;
  }
}

class Constructor {
  index: number;
  inductive: Inductive;
  constructor(ind: Inductive, i: number) {
    this.index = i;
    this.inductive = ind;
  }
}

class Notation { }

class NotationRoot extends Notation {
  notationRule: Notation_Rule;
  substitutions: Substitutions;
  constructor(nr: Notation_Rule, subst: Substitutions) {
    super();
    this.notationRule = nr;
    this.substitutions = subst;
  }
}

class NotationPiece extends Notation { }

class NotNotation extends Notation { }

class Notation_Rule {
  interpRule: InterpRule;
  interpretation: Interpretation;
  int: number; // nullable
  constructor(interpRule: InterpRule, interpretation: Interpretation, i: number) {
    this.interpRule = interpRule;
    this.interpretation = interpretation;
    this.int = i;
  }
}

class Interpretation {
  list: Array<Array<any>>; // could be made an Object
  notationConstr: NotationConstr;
  constructor(a: Array<Array<any>>, n: NotationConstr) {
    this.list = a;
    this.notationConstr = n;
  }
}

class InterpRule { }

class NotationRule extends InterpRule {
  notation: string;
  precedence: number;
  scopeName: string; // nullable
  unparsing: Array<Unparsing>;
  constructor(s: string, n: string, unpl: Array<Unparsing>, prec: number) {
    super();
    this.scopeName = s;
    this.notation = n;
    this.unparsing = unpl;
    this.precedence = prec;
  }
}

class SynDefRule extends InterpRule {
  kernelName: string;
  constructor(k: string) {
    super();
    this.kernelName = k;
  }
}

class NotationConstr { }

class NRef extends NotationConstr {
  globalReference: GlobalReference;
  constructor(gr: GlobalReference) {
    super();
    this.globalReference = gr;
  }
}

class NVar extends NotationConstr {
  id: string;
  constructor(id: string) {
    super();
    this.id = id;
  }
}

class NApp extends NotationConstr {
  function: NotationConstr;
  arguments: Array<NotationConstr>;
  constructor(nc: NotationConstr, ncl: Array<NotationConstr>) {
    super();
    this.function = nc;
    this.arguments = ncl;
  }
}

class NHole extends NotationConstr {
  constructor() {
    super();
  }
}

class NList extends NotationConstr {
  constructor() {
    super();
  }
}

class NLambda extends NotationConstr {
  constructor() {
    super();
  }
}

class NProd extends NotationConstr {
  binder: string;
  binderType: NotationConstr;
  body: NotationConstr;
  constructor(name: string, nc1: NotationConstr, nc2: NotationConstr) {
    super();
    this.binder = name;
    this.binderType = nc1;
    this.body = nc2;
  }
}

class NBinderList extends NotationConstr {
  constructor() {
    super();
  }
}

class NLetIn extends NotationConstr {
  constructor() {
    super();
  }
}

class NCases extends NotationConstr {
  constructor() {
    super();
  }
}

class NLetTuple extends NotationConstr {
  constructor() {
    super();
  }
}

class NIf extends NotationConstr {
  constructor() {
    super();
  }
}

class NRec extends NotationConstr {
  constructor() {
    super();
  }
}

class NSort extends NotationConstr {
  constructor() {
    super();
  }
}

class NPatVar extends NotationConstr {
  constructor() {
    super();
  }
}

class NCast extends NotationConstr {
  constructor() {
    super();
  }
}

class NotationVarInstanceType { }

class NtnTypeConstr extends NotationVarInstanceType { }

class NtnTypeConstrList extends NotationVarInstanceType { }

class NtnTypeBinderList extends NotationVarInstanceType { }

class Reference { }
class Qualid extends Reference {
  qualid: string;
  ppQualid: string;
  constructor(q: string, pp: string) {
    super();
    this.qualid = q;
    this.ppQualid = pp;
  }
}
class Ident extends Reference {
  id: string;
  constructor(id: string) {
    super();
    this.id = id;
  }
}

function precLess(child: number, parent: PrecAssoc) {
  if (parent.precedence < 0 && child === lProd) {
    return true;
  }
  var parentPrec = Math.abs(parent.precedence);
  var parentAssoc = parent.associativity;
  if (parentAssoc instanceof E) { return child <= parentPrec; }
  if (parentAssoc instanceof L) { return child < parentPrec; }
  if (parentAssoc instanceof Prec) { return child <= parentAssoc.precedence; }
  if (parentAssoc instanceof Any) { return true; }
}

class Unparsing { }

class UnpMetaVar extends Unparsing {
  index: number;
  parenRelation: Associativity;
  constructor(i: number, p: Associativity) {
    super();
    this.index = i;
    this.parenRelation = p;
  }
}

class UnpListMetaVar extends Unparsing {
  index: number;
  parenRelation: Associativity;
  unparsing: Array<Unparsing>;
  constructor(i: number, pr: Associativity, unpl: Array<Unparsing>) {
    super();
    this.index = i;
    this.parenRelation = pr;
    this.unparsing = unpl;
  }
}

class UnpBinderListMetaVar extends Unparsing {
  // TODO
}

class UnpTerminal extends Unparsing {
  terminal: string;
  constructor(s: string) {
    super();
    this.terminal = s;
  }
}

class UnpBox extends Unparsing {
  box: PpBox;
  unparsing: Array<Unparsing>;
  constructor(b: PpBox, unpl: Array<Unparsing>) {
    super();
    this.box = b;
    this.unparsing = unpl;
  }
}

class PpBox { }

class PpHB extends PpBox {
  constructor(a: number) {
    super();
    // TODO
  }
}

class PpHOVB extends PpBox {
  constructor(a: number) {
    super();
    // TODO
  }
}

class PpHVB extends PpBox {
  constructor(a: number) {
    super();
    // TODO
  }
}

class PpVB extends PpBox {
  constructor(a: number) {
    super();
    // TODO
  }
}

class PpTB extends PpBox { }

class UnpCut extends Unparsing {
  cut: PpCut;
  constructor(c: PpCut) {
    super();
    this.cut = c;
  }
}

class PpCut { }

class PpBrk extends PpCut {
  constructor(a: number, b: number) {
    super();
    // TODO
  }
}

class PpTbrk extends PpCut {
  // TODO
}

class PpTab extends PpCut {
  // TODO
}

class PpFnl extends PpCut {
  // TODO
}

function tagUnparsing(unp, pp1): string {
  return pp1;
}

function PpCmdOfBox(b, s): string { return s; }

function PpCmdOfCut(c): string { return " "; }

function printHunks(n: number, pp: (pa: PrecAssoc, c: Term) => string, ppBinders, subst: Substitutions, unps) {
  var env = _.clone(subst.subterms);
  var envlist = _.clone(subst.notations);
  var bll = _.clone(subst.binders);
  function ret(unp, pp1, pp2) {
    return (tagUnparsing(unp, pp1) + pp2);
  }
  function aux(unpl): string {
    if (unpl.length === 0) {
      return "";
    } else {
      var rest = _.rest(unpl);
      var u = unpl[0];
      var pp1, pp2: string;

      if (u instanceof UnpMetaVar) {
        var prec = u.parenRelation;
        var c = env.shift();
        if (c === undefined) {
          throw "Environment exhausted!";
        }
        pp2 = aux(rest);
        pp1 = pp(new PrecAssoc(n, prec), c);
        return ret(u, pp1, pp2);
      }

      if (u instanceof UnpListMetaVar) {
        var prec = u.parenRelation;
        var cl = envlist.shift();
        var ppTerm : (t: Term) => string = (t) => pp(new PrecAssoc(n, prec), t);
        pp1 = ppListWithSep(() => aux(u.unparsing), ppTerm, cl);
        pp2 = aux(rest);
        return ret(u, pp1, pp2);
      }

      if (u instanceof UnpBinderListMetaVar) {
        return "TODO3";
      }

      if (u instanceof UnpTerminal) {
        pp2 = aux(rest);
        pp1 = u.terminal;
        return ret(u, pp1, pp2);
      }

      if (u instanceof UnpBox) {
        pp1 = PpCmdOfBox(u.box, aux(u.unparsing));
        pp2 = aux(rest);
        return ret(u, pp1, pp2);
      }

      if (u instanceof UnpCut) {
        pp2 = aux(rest);
        pp1 = PpCmdOfCut(u.cut);
        return ret(u, pp1, pp2);
      }

      throw "Error: Unknown Unparsing instance";
    }
  }
  return aux(unps);
}

class Substitutions {
  subterms: Array<Term>;
  notations: Array<Array<Term>>;
  binders: Array<Array<LocalBinder>>;
  constructor(
    s: Array<Term>, n: Array<Array<Term>>, b: Array<Array<LocalBinder>>
    ) {
    this.subterms = s;
    this.notations = n;
    this.binders = b;
  }
}

class LocalBinder { }

class LocalRawDef extends LocalBinder {
  binderName: string;
  binderType: Term;
  constructor(n: string, t: Term) {
    super();
    this.binderName = n;
    this.binderType = t;
  }
}

class LocalRawAssum extends LocalBinder {
  names: Array<string>;
  binderKind: BinderKind;
  term: Term;
  constructor(l: Array<string>, bk: BinderKind, t: Term) {
    super();
    this.names = l;
    this.binderKind = bk;
    this.term = t;
  }
}

class BinderKind { }

class Default extends BinderKind {
  kind: BindingKind;
  constructor(bk: BindingKind) {
    super();
    this.kind = bk;
  }
}

class Generalized extends BinderKind {
  kind1: BindingKind;
  kind2: BindingKind;
  b: boolean;
  constructor(bk1: BindingKind, bk2: BindingKind, b: boolean) {
    super();
    this.kind1 = bk1;
    this.kind2 = bk2;
    this.b = b;
  }
}

class BindingKind { }
class Explicit extends BindingKind { }
class Implicit extends BindingKind { }

class PrimToken { }

class Numeral extends PrimToken {
  numeral: number;
  constructor(n: number) {
    super();
    this.numeral = n;
  }
  pp(): string { return this.numeral.toString(); }
  prec(): number { return (this.numeral >= 0) ? lPosInt : lNegInt; }
}

class PrimTokenString extends PrimToken {
  string: string;
  constructor(s: string) {
    super();
    this.string = s;
  }
  pp(): string { return this.string; }
  prec(): number { return lAtom; }
}

var term = new App(new NotationRoot(new Notation_Rule(new NotationRule("type_scope", "_ = _", [new UnpBox(new PpHOVB(0), [new UnpMetaVar(1, new L()), new UnpTerminal(" ="), new UnpCut(new PpBrk(1, 0)), new UnpMetaVar(2, new L())])], 70), new Interpretation([["x", [null, []], new NtnTypeConstr()], ["y", [null, []], new NtnTypeConstr()]], new NApp(new NRef(new IndRef(new Inductive("Coq.Init.Logic.eq", 0))), [new NHole(), new NVar("x"), new NVar("y")])), 3), new Substitutions([new Ref(new NotNotation(), new ConstructRef(new Constructor(new Inductive("Coq.Init.Datatypes.nat", 0), 1)), new Qualid("O", "O"), "O"), new Prim(new NotNotation(), new Numeral(1))], [], [])), new Ref(new NotationPiece(), new IndRef(new Inductive("Coq.Init.Logic.eq", 0)), new Qualid("eq", "eq"), "eq"), [new Hole(new NotationPiece()), new Ref(new NotationPiece(), new ConstructRef(new Constructor(new Inductive("Coq.Init.Datatypes.nat", 0), 1)), new Qualid("O", "O"), "O"), new App(new NotationPiece(), new Ref(new NotationPiece(), new ConstructRef(new Constructor(new Inductive("Coq.Init.Datatypes.nat", 0), 2)), new Qualid("S", "S"), "S"), [new Ref(new NotationPiece(), new ConstructRef(new Constructor(new Inductive("Coq.Init.Datatypes.nat", 0), 1)), new Qualid("O", "O"), "O")])]);
