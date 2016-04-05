// import BindingKind from "./binding-kind";

abstract class BinderKind { }

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
