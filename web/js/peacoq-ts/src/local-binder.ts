import BinderKind from "./binder-kind";
import ConstrExpr from "./coq-constr-expr";
import { Located } from "./coq-definitions";
import NameBase from "./name-base";

export default LocalBinder;

export abstract class LocalBinder { }

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
