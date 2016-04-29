// import ParenRelation from "./paren-relation";
// import PpBox from "./ppbox";
// import PpCut from "./ppcut";

abstract class Unparsing { }

class UnpMetaVar extends Unparsing {
  constructor(
    public index: number,
    public parenRelation: ParenRelation
  ) {
    super();
  }
}

class UnpListMetaVar extends Unparsing {
  constructor(
    public index: number,
    public parenRelation: ParenRelation,
    public unparsing: Unparsing[]
  ) {
    super();
  }
}

class UnpBinderListMetaVar extends Unparsing {
  constructor(
    public n: number,
    public isOpen: boolean,
    public unparsing: Unparsing[]
  ) {
    super();
  }
}

class UnpTerminal extends Unparsing {
  constructor(
    public terminal: string
  ) {
    super();
  }
}

class UnpBox extends Unparsing {
  constructor(
    public box: PpBox,
    public unparsing: Unparsing[]
  ) {
    super();
  }
}

class UnpCut extends Unparsing {
  constructor(public cut: PpCut) {
    super();
  }
}
