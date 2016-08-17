// import BindingKind from "./binding-kind";

abstract class BinderKind { }

class Default extends BinderKind {
  constructor(
    public kind: BindingKind
  ) {
    super();
  }
}

class Generalized extends BinderKind {
  constructor(
    public kind1: BindingKind,
    public kind2: BindingKind,
    public b: boolean
  ) {
    super();
  }
}
