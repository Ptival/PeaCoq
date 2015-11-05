class ParenRelation {}
class E extends ParenRelation {}
class L extends ParenRelation {}
class Prec extends ParenRelation {
  precedence: number;
  constructor(prec: number) {
    super();
    this.precedence = prec;
  }
}
class Any extends ParenRelation {}

type PrecAssoc =[number, ParenRelation];

type CoqLocation =[number, number];

class GlobSortGen<T> {}
class GProp<T> extends GlobSortGen<T> {}
class GSet<T> extends GlobSortGen<T> {}
class GType<T> extends GlobSortGen<T> {
  type: T;
  constructor(t: T) {
    super();
    this.type = t;
  }
}

type LevelInfo = Maybe<string>;
type GlobLevel = GlobSortGen<LevelInfo>;
type SortInfo = string[];
type GlobSort = GlobSortGen<SortInfo>;

type InstanceExpr = Array<GlobLevel>;

type Located<T> = [CoqLocation, T];

class Reference {}

type QualId =[Array<string>, string];

class Qualid extends Reference {
  lQualid: Located<QualId>;
  constructor(q: Located<QualId>) {
    super();
    this.lQualid = q;
  }
}

class Ident extends Reference {
  id: Located<string>;
  constructor(id: Located<string>) {
    super();
    this.id = id;
  }
}

class BinderKind {}

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

class NameBase {}

class Name extends NameBase {
  id: string;
  constructor(id: string) {
    super();
    this.id = id;
  }
}

class Anonymous extends NameBase {}

class LocalBinder {}

class LocalRawDef extends LocalBinder {
  binderName: Located<NameBase>;
  binderType: ConstrExpr;
  constructor(n: Located<NameBase>, t: ConstrExpr) {
    super();
    this.binderName = n;
    this.binderType = t;
  }
}

class LocalRawAssum extends LocalBinder {
  names: Array<Located<NameBase>>;
  binderKind: BinderKind;
  term: ConstrExpr;
  constructor(l: Array<Located<NameBase>>, bk: BinderKind, t: ConstrExpr) {
    super();
    this.names = l;
    this.binderKind = bk;
    this.term = t;
  }
}

class BindingKind {}
class Explicit extends BindingKind {}
class Implicit extends BindingKind {}

class Unparsing {}

class UnpMetaVar extends Unparsing {
  index: number;
  parenRelation: ParenRelation;
  constructor(i: number, p: ParenRelation) {
    super();
    this.index = i;
    this.parenRelation = p;
  }
}

class UnpListMetaVar extends Unparsing {
  index: number;
  parenRelation: ParenRelation;
  unparsing: Array<Unparsing>;
  constructor(i: number, pr: ParenRelation, unpl: Array<Unparsing>) {
    super();
    this.index = i;
    this.parenRelation = pr;
    this.unparsing = unpl;
  }
}

class UnpBinderListMetaVar extends Unparsing {
  n: number;
  isOpen: boolean;
  unparsing: Unparsing[];
  constructor(n, b, ul) {
    super();
    this.n = n;
    this.isOpen = b;
    this.unparsing = ul;
  }
}

class UnpTerminal extends Unparsing {
  terminal: string;
  constructor(s: string) {
    super();
    // replace NBSP with whitespace
    //this.terminal = s.replace(/\u00A0/g, " ");
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

class PpBox {}

class PpHB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpHoVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpHVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpTB extends PpBox {}

class UnpCut extends Unparsing {
  cut: PpCut;
  constructor(c: PpCut) {
    super();
    this.cut = c;
  }
}

class PpCut {}

class PpBrk extends PpCut {
  n1: number; n2: number;
  constructor(a: number, b: number) { super(); this.n1 = a; this.n2 = b; }
}

class PpTbrk extends PpCut {
  n1: number; n2: number;
  constructor(a: number, b: number) { super(); this.n1 = a; this.n2 = b; }
}

class PpTab extends PpCut {}

class PpFnl extends PpCut {}

function tagUnparsing(unp: Unparsing, pp1: PpCmds): PpCmds {
  if (unp instanceof UnpTerminal) {
    return tagNotation(pp1);
  }
  return pp1;
}

function h(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHBox(n), s)]; }
function v(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpVBox(n), s)]; }
function hv(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHVBox(n), s)]; }
function hov(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHoVBox(n), s)]; }
function t(s: PpCmds): PpCmds { return [new PpCmdBox(new PpTBox(), s)]; }

function PpCmdOfBox(b: PpBox, s: PpCmds): PpCmds {
  if (b instanceof PpHB) { return h(b.n, s); }
  if (b instanceof PpHoVB) { return hov(b.n, s); }
  if (b instanceof PpHVB) { return hv(b.n, s); }
  if (b instanceof PpVB) { return v(b.n, s); }
  if (b instanceof PpTB) { return t(s); }
  throw MatchFailure("PpCmdOfBox", b);
}

function tab(): PpCmds { return [new PpCmdSetTab()]; }
function fnl(): PpCmds { return [new PpCmdForceNewline()]; }
function brk(a, b): PpCmds { return [new PpCmdPrintBreak(a, b)]; }
function tbrk(a, b): PpCmds { return [new PpCmdPrintTbreak(a, b)]; }

function PpCmdOfCut(c: PpCut): PpCmds {
  if (c instanceof PpTab) { return tab(); }
  if (c instanceof PpFnl) { return fnl(); }
  if (c instanceof PpBrk) { return brk(c.n1, c.n2); }
  if (c instanceof PpTbrk) { return tbrk(c.n1, c.n2); }
  throw MatchFailure("PpCmdOfCut", c);
}

class PrimToken {}

class Numeral extends PrimToken {
  numeral: number;
  constructor(n: number) {
    super();
    this.numeral = n;
  }
}

class PrimTokenString extends PrimToken {
  string: string;
  constructor(s: string) {
    super();
    this.string = s;
  }
}

class CaseStyle {}
class LetStyle extends CaseStyle {}
class IfStyle extends CaseStyle {}
class LetPatternStyle extends CaseStyle {}
class MatchStyle extends CaseStyle {}
class RegularStyle extends CaseStyle {}

class CasesPatternExpr {}
// TODO

class BlockType {}
class PpHBox extends BlockType {
  constructor(x: number) {
    super();
  }
}
class PpVBox extends BlockType {
  constructor(x: number) {
    super();
  }
}
class PpHVBox extends BlockType {
  constructor(x: number) {
    super();
  }
}
class PpHoVBox extends BlockType {
  constructor(x: number) {
    super();
  }
}
class PpTBox extends BlockType {}
