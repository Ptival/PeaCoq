//
// type PP = (pa: PrecAssoc, a: Term) => string;
//
// function ppListSepLastSep<T>(noEmpty: boolean, sep: () => string, lastSep: () => string, elem: (t: T) => string) {
//   var start = function(a) {
//     if (a.length === 0) { return ""; }
//     else if (a.length === 1) { return elem(a[0]); }
//     else {
//       var e = elem(a[0]);
//       var t = _.rest(a);
//       if (noEmpty && e === "") {
//         return start(t);
//       } else {
//         var aux = function(a) {
//           if (a.length === 0) {
//             return "";
//           } else {
//             var e = elem(a[0]);
//             var r = aux(_.rest(a));
//             if (noEmpty && e === "") {
//               return r;
//             } else {
//               if (r === "") {
//                 return lastSep() + e;
//               } else {
//                 return sep() + e + r;
//               }
//             }
//           }
//         };
//         return e + aux(t);
//       }
//     }
//   }
//   return start;
// }
//
// function ppListWithSep<T>(sep: () => string, pr: (t: T) => string, l: Array<T>) {
//   return ppListSepLastSep(false, sep, sep, pr)(l);
// }
//
// function ppList<T>(pp: (t: T) => string, l: Array<T>): string {
//   return _(l).reduce(function(acc, elt) { return acc + pp(elt); }, "");
// }
//
// function ppSepCom(sep: string, f: (pa: PrecAssoc) => string, pa: PrecAssoc) {
//   return sep + f(pa);
// }
//
// function ppExplArgs(pp: PP, a: Term): string {
//   // TODO: explicitation
//   return pp(new PrecAssoc(lApp, new L()), a);
// }
//
// function ppQualid(qualid: Qualid): string {
//   return qualid.ppQualid;
// }
//
// function ppReference(ref): string {
//   if (ref instanceof Qualid) {
//     return ppQualid(ref);
//   }
//   if (ref instanceof Ident) {
//     return ref.id;
//   }
//   throw "ppReference";
// }
//
// function ppRef(ref: Reference): string {
//   // TODO: universe instance
//   return ppReference(ref);
// }
//
// function ppApp(pp: PP, a: Term, l: Array<Term>) {
//   return (
//     pp(new PrecAssoc(lApp, new L()), a)
//     + ppList((a) => { return " " + ppExplArgs(pp, a); }, l)
//     );
// }
//
// type PpResult = { string: string; precedence: number };
//
// function ppBinder(many: boolean, pp, o) {
//   var names = o.names;
//   var binderKind = o.binderKind;
//   var term = o.term;
//   if (binderKind instanceof Generalized) {
//     return "TODO: Generalized";
//   }
//   if (binderKind instanceof Default) {
//     return "TODO: Default";
//   }
//   throw MatchFailure("ppBinder", binderKind);
// }
//
// function ppBinderAmongMany(
//   ppC,
//   //b: LocalBinder
//   t: Term
//  ) {
//    return prettyPrint(t);
//    /*
//   if (b instanceof LocalRawAssum) {
//     return ppBinder(true, ppC, {
//       names: b.names,
//       binderKind: b.binderKind,
//       term: b.term,
//     })
//   }
//   if (b instanceof LocalRawDef) {
//     return "TODO: LocalRawDef";
//   }
//   throw MatchFailure("ppBinderAmongMany", b);
//   */
// }
//
// function ppUndelimitedBinders(sep, ppC, c) {
//   //return ppListWithSep(sep, ppBinderAmongMany(ppC));
//   return "TODO";
// }
//
// function ppDelimitedBinders(
//   kw: () => string, sep: () => string, ppC: (t: Term) => string,
//   //bl: Array<LocalBinder>
//   tl: Array<Term>
// ) {
//   // TODO: implement this correctly
//   return kw() + ppListWithSep(sep, (b) => ppBinderAmongMany(ppC, b), tl);
// }
//
// function ppBindersGen(ppC: (t: Term) => string, sep, isOpen) {
//   if (isOpen) {
//     return (bl) => ppDelimitedBinders(() => "", sep, ppC, bl);
//   } else {
//     return (bl) => ppUndelimitedBinders(sep, ppC, bl);
//   }
// }
//
// function ppForall() {
//   return "forall ";
// }
//
// function pp(pp): (sep: string, inherited: PrecAssoc, a: Term) => string {
//   return function(sep, inherited, a): string {
//
//     function ret(s: string, p: number): PpResult {
//       return {
//         string: s,
//         precedence: p,
//       }
//     }
//
//     function match(a: Term): PpResult {
//
//       var annot = a.annotation;
//       if (annot instanceof NotationRoot) {
//         var notation_Rule = annot.notationRule;
//         var substitutions = annot.substitutions;
//         var ir = notation_Rule.interpRule;
//
//         if (ir instanceof NotationRule) {
//           var level = ir.precedence;
//           var ppBinders =
//             _.partial(
//               ppBindersGen,
//               _.partial(pp, "", lTop)
//               );
//
//           return ret(
//             printHunks(
//               level,
//               (pa, c) => pp("", pa, c),
//               ppBinders,
//               substitutions,
//               ir.unparsing
//               ),
//             level);
//         }
//
//         if (ir instanceof SynDefRule) {
//           var sdr = <SynDefRule>ir;
//           throw "TODO: SynDefRule";
//         }
//
//         throw "match";
//       }
//
//       if (a instanceof Ref) {
//         return ret(ppRef(a.reference), lAtom);
//       }
//
//       if (a instanceof App) {
//         return ret(
//           ppApp(
//             (inherited, number) => pp("", inherited, number),
//             a.function,
//             a.arguments
//             ),
//           lApp
//           );
//       }
//
//       if (a instanceof Prim) {
//         var p = a.prim;
//         return ret(p.pp(), p.prec());
//       }
//
//       if (a instanceof Hole) {
//         return ret("_", lAtom);
//       }
//
//       if (a instanceof Prod) {
//         var pb = extractProdBinders(a);
//         return ret(
//           ppDelimitedBinders(
//             ppForall,
//             () => "",
//             (n) => pp("", lTop, n),
//             pb.binderList
//             )
//           + ", " + pp(" ", lTop, pb.remainingTerm),
//           lProd);
//       }
//
//       if (a instanceof Var) {
//         // TODO: check if this is correct
//         return ret(a.name, lAtom);
//       }
//
//       throw ("match failed! " + a.constructor.toString());
//     }
//
//     var matchResult = match(a);
//
//     if (precLess(matchResult.precedence, inherited)) {
//       return matchResult.string;
//     } else {
//       return "(" + matchResult.string + ")";
//     }
//
//   }
// }
//
// function fix(f) {
//   return function(...x) {
//     return f(fix(f))(...x);
//   }
// };
//
// function prettyPrint(a: Term): string {
//   return fix(pp)("", lTop, a);
// }
//
// class Term {
//   annotation: Notation;
//   constructor(a: Notation) {
//     this.annotation = a;
//   }
// }
//
// class Ref extends Term {
//   baseName: string;
//   globalReference: GlobalReference;
//   reference: Reference;
//   constructor(a: Notation, gr: GlobalReference, r: Reference, baseName: string) {
//     super(a);
//     this.baseName = baseName;
//     this.globalReference = gr;
//     this.reference = r;
//   }
// }
//
// class Var extends Term {
//   name: string;
//   constructor(a: Notation, n: Name) {
//     super(a);
//     this.name = name;
//   }
// }
//
// class Evar extends Term {
//   // TODO
// }
//
// class PatVar extends Term {
//   // TODO
// }
//
// class App extends Term {
//   function: Term;
//   arguments: Array<Term>;
//   constructor(a: Notation, t: Term, tl: Array<Term>) {
//     super(a);
//     this.function = t;
//     this.arguments = tl;
//   }
// }
//
// class Lambda extends Term {
//   // TODO
// }
//
// class Prod extends Term {
//   t1: Term;
//   t2: Term;
//   constructor(a: Notation, t1: Term, t2: Term) {
//     super(a);
//     this.t1 = t1;
//     this.t2 = t2;
//   }
// }
//
// class LetIn extends Term {
//   // TODO
// }
//
// class Cases extends Term {
//   // TODO
// }
//
// class LetTuple extends Term {
//   // TODO
// }
//
// class If extends Term {
//   // TODO
// }
//
// class Rec extends Term {
//   // TODO
// }
//
// class Sort extends Term {
//   // TODO
// }
//
// class Hole extends Term {
//   constructor(a: Notation) {
//     super(a);
//   }
// }
//
// class Cast extends Term {
//   // TODO
// }
//
// class Prim extends Term {
//   prim: PrimToken;
//   constructor(a: Notation, pt: PrimToken) {
//     super(a);
//     this.prim = pt;
//   }
// }
//
// class GlobalReference { }
//
// class VarRef extends GlobalReference {
//   variable: string;
//   constructor(v: string) {
//     super();
//     this.variable = v;
//   }
// }
//
// class ConstRef extends GlobalReference {
//   constant: string;
//   constructor(c: string) {
//     super();
//     this.constant = c;
//   }
// }
//
// class IndRef extends GlobalReference {
//   inductive: Inductive;
//   constructor(i: Inductive) {
//     super();
//     this.inductive = i;
//   }
// }
//
// class ConstructRef extends GlobalReference {
//   construct: Constructor;
//   constructor(c: Constructor) {
//     super();
//     this.construct = c;
//   }
// }
//
// class Inductive {
//   index: number;
//   name: string;
//   constructor(name: string, index: number) {
//     this.name = name;
//     this.index = index;
//   }
// }
//
// class Constructor {
//   index: number;
//   inductive: Inductive;
//   constructor(ind: Inductive, i: number) {
//     this.index = i;
//     this.inductive = ind;
//   }
// }
//
// class Notation { }
//
// class NotationRoot extends Notation {
//   notationRule: Notation_Rule;
//   substitutions: Substitutions;
//   constructor(nr: Notation_Rule, subst: Substitutions) {
//     super();
//     this.notationRule = nr;
//     this.substitutions = subst;
//   }
// }
//
// class NotationPiece extends Notation { }
//
// class NotNotation extends Notation { }
//
// class Notation_Rule {
//   interpRule: InterpRule;
//   interpretation: Interpretation;
//   int: number; // nullable
//   constructor(interpRule: InterpRule, interpretation: Interpretation, i: number) {
//     this.interpRule = interpRule;
//     this.interpretation = interpretation;
//     this.int = i;
//   }
// }
//
// class Interpretation {
//   list: Array<Array<any>>; // could be made an Object
//   notationConstr: NotationConstr;
//   constructor(a: Array<Array<any>>, n: NotationConstr) {
//     this.list = a;
//     this.notationConstr = n;
//   }
// }
//
// class InterpRule { }
//
//class NotationRule extends InterpRule {
//  notation: string;
//  precedence: number;
//  scopeName: string; // nullable
//  unparsing: Array<Unparsing>;
//  constructor(s: string, n: string, unpl: Array<Unparsing>, prec: number) {
//    super();
//    this.scopeName = s;
//    this.notation = n;
//    this.unparsing = unpl;
//    this.precedence = prec;
//  }
//}
//
//class SynDefRule extends InterpRule {
//  kernelName: string;
//  constructor(k: string) {
//    super();
//    this.kernelName = k;
//  }
//}
//
//class NotationConstr { }
//
//class NRef extends NotationConstr {
//  globalReference: GlobalReference;
//  constructor(gr: GlobalReference) {
//    super();
//    this.globalReference = gr;
//  }
//}
//
//class NVar extends NotationConstr {
//  id: string;
//  constructor(id: string) {
//    super();
//    this.id = id;
//  }
//}
//
//class NApp extends NotationConstr {
//  function: NotationConstr;
//  arguments: Array<NotationConstr>;
//  constructor(nc: NotationConstr, ncl: Array<NotationConstr>) {
//    super();
//    this.function = nc;
//    this.arguments = ncl;
//  }
//}
//
//class NHole extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NList extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NLambda extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NProd extends NotationConstr {
//  binder: string;
//  binderType: NotationConstr;
//  body: NotationConstr;
//  constructor(name: string, nc1: NotationConstr, nc2: NotationConstr) {
//    super();
//    this.binder = name;
//    this.binderType = nc1;
//    this.body = nc2;
//  }
//}
//
//class NBinderList extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NLetIn extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NCases extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NLetTuple extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NIf extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NRec extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NSort extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NPatVar extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NCast extends NotationConstr {
//  constructor() {
//    super();
//  }
//}
//
//class NotationVarInstanceType { }
//
//class NtnTypeConstr extends NotationVarInstanceType { }
//
//class NtnTypeConstrList extends NotationVarInstanceType { }
//
//class NtnTypeBinderList extends NotationVarInstanceType { }
//
//
//function printHunks(n: number, pp: (pa: PrecAssoc, c: Term) => string, ppBinders, subst: Substitutions, unps) {
//  var env = _.clone(subst.subterms);
//  var envlist = _.clone(subst.notations);
//  var bll = _.clone(subst.binders);
//  function ret(unp, pp1, pp2) {
//    return (tagUnparsing(unp, pp1) + pp2);
//  }
//  function aux(unpl): string {
//    if (unpl.length === 0) {
//      return "";
//    } else {
//      var rest = _.rest(unpl);
//      var u = unpl[0];
//      var pp1, pp2: string;
//
//      if (u instanceof UnpMetaVar) {
//        var prec = u.parenRelation;
//        var c = env.shift();
//        if (c === undefined) {
//          throw "Environment exhausted!";
//        }
//        pp2 = aux(rest);
//        pp1 = pp(new PrecAssoc(n, prec), c);
//        return ret(u, pp1, pp2);
//      }
//
//      if (u instanceof UnpListMetaVar) {
//        var prec = u.parenRelation;
//        var cl = envlist.shift();
//        var ppTerm: (t: Term) => string = (t) => pp(new PrecAssoc(n, prec), t);
//        pp1 = ppListWithSep(() => aux(u.unparsing), ppTerm, cl);
//        pp2 = aux(rest);
//        return ret(u, pp1, pp2);
//      }
//
//      if (u instanceof UnpBinderListMetaVar) {
//        return "TODO3";
//      }
//
//      if (u instanceof UnpTerminal) {
//        pp2 = aux(rest);
//        pp1 = u.terminal;
//        return ret(u, pp1, pp2);
//      }
//
//      if (u instanceof UnpBox) {
//        pp1 = PpCmdOfBox(u.box, aux(u.unparsing));
//        pp2 = aux(rest);
//        return ret(u, pp1, pp2);
//      }
//
//      if (u instanceof UnpCut) {
//        pp2 = aux(rest);
//        pp1 = PpCmdOfCut(u.cut);
//        return ret(u, pp1, pp2);
//      }
//
//      throw "Error: Unknown Unparsing instance";
//    }
//  }
//  return aux(unps);
//}
//
//class Substitutions {
//  subterms: Array<Term>;
//  notations: Array<Array<Term>>;
//  binders: Array<Array<LocalBinder>>;
//  constructor(
//  //s: Array<Term>, n: Array<Array<Term>>, b: Array<Array<LocalBinder>>
//    ) {
//    //this.subterms = s;
//    //this.notations = n;
//    //this.binders = b;
//  }
//}
//
//
//
//class PrimToken {
//  pp(): string { throw "To be overridden"; };
//  prec(): number { throw "To be overridden"; };
//}
//
//class Numeral extends PrimToken {
//  numeral: number;
//  constructor(n: number) {
//    super();
//    this.numeral = n;
//  }
//  pp(): string { return this.numeral.toString(); }
//  prec(): number { return (this.numeral >= 0) ? lPosInt : lNegInt; }
//}
//
//class PrimTokenString extends PrimToken {
//  string: string;
//  constructor(s: string) {
//    super();
//    this.string = s;
//  }
//  pp(): string { return this.string; }
//  prec(): number { return lAtom; }
//}
//
//type ExtractProdBinders = {
//  //binderList : Array<LocalBinder>;
//  binderList: Array<Term>;
//  remainingTerm: Term;
//}
//
//function extractProdBinders(a: Term): ExtractProdBinders {
//  if (a instanceof Prod) {
//    var rest = extractProdBinders(a.t2);
//    return {
//      binderList: [a.t1].concat(rest.binderList),
//      remainingTerm: rest.remainingTerm,
//    };
//  }
//  return {
//    binderList: [],
//    remainingTerm: a
//  };
//}
//
//function MatchFailure(fn: string, o: Object) {
//  return ("match failed in " + fn + ", constructor: " + o.constructor.toString());
//}
