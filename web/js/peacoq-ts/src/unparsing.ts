import ParenRelation from "./paren-relation";
import PpBox from "./ppbox";
import PpCut from "./ppcut";

export default Unparsing;

export abstract class Unparsing { }

export class UnpMetaVar extends Unparsing {
  index: number;
  parenRelation: ParenRelation;
  constructor(i: number, p: ParenRelation) {
    super();
    this.index = i;
    this.parenRelation = p;
  }
}

export class UnpListMetaVar extends Unparsing {
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

export class UnpBinderListMetaVar extends Unparsing {
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

export class UnpTerminal extends Unparsing {
  terminal: string;
  constructor(s: string) {
    super();
    // replace NBSP with whitespace
    //this.terminal = s.replace(/\u00A0/g, " ");
    this.terminal = s;
  }
}

export class UnpBox extends Unparsing {
  box: PpBox;
  unparsing: Array<Unparsing>;
  constructor(b: PpBox, unpl: Array<Unparsing>) {
    super();
    this.box = b;
    this.unparsing = unpl;
  }
}

export class UnpCut extends Unparsing {
  cut: PpCut;
  constructor(c: PpCut) {
    super();
    this.cut = c;
  }
}
