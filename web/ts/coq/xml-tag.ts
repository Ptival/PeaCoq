abstract class CoqXMLTag { }

function mkCoqXMLTag(t): CoqXMLTag {
  let c = t.contents;
  switch (t.tag) {
    case "Apply":
      return new Apply();
    case "Constant":
      return new Constant(c);
    case "Definition":
      return new Definition(c[0], c[1]);
    case "Gallina":
      return new Gallina();
    case "Ltac":
      return new Ltac(c);
    case "Operator":
      return new Operator(c[0], c[1]);
    case "Proof":
      return new Proof();
    case "QED":
      return new QED();
    case "Recurse":
      return new Recurse();
    case "SectionSubsetDescr":
      return new SectionSubsetDescr(c);
    case "Theorem":
      return new Theorem(c[0], c[1]);
    case "Token":
      return new Token(c);
    case "Typed":
      return new Typed();
    default:
      throw ("Unknown CoqXMLTag: " + t.tag);
  };
}

class Apply extends CoqXMLTag {
  toString() { return "Apply"; }
}

class Constant extends CoqXMLTag {
  constructor(public constant: string) { super(); }
  toString() { return "Constant(" + this.constant + ")"; }
}

class Definition extends CoqXMLTag {
  constructor(public a: string, public b: string) {
    super();
  }
  toString() {
    return "Definition(" + this.a + ", " + this.b + ")";
  }
}

class Gallina extends CoqXMLTag {
  toString = function() { return "Gallina"; }
}

class Ltac extends CoqXMLTag {
  constructor(public s: string) {
    super();
  }
  toString() { return "Ltac(" + this.s + ")"; }
}

class Operator extends CoqXMLTag {
  constructor(public s: string, public ms: string) { super(); }
  toString() { return "Operator(" + this.s + ", " + this.ms + ")"; }
}

class Proof extends CoqXMLTag {
  toString() { return "Proof"; }
}

class QED extends CoqXMLTag {
  toString() { return "QED"; }
}

class Recurse extends CoqXMLTag {
  toString() { return "Recurse"; }
}

class SectionSubsetDescr extends CoqXMLTag {
  constructor(public s: string) { super(); }
  toString() { return "SectionSubsetDescr(" + this.s + ")"; }
}

class Theorem extends CoqXMLTag {
  constructor(public a: string, public b: string) { super(); }
  toString() { return "Theorem(" + this.a + ", " + this.b + ")"; }
}

class Token extends CoqXMLTag {
  constructor(public s: string) { super(); }
  toString() { return "Token(" + this.s + ")"; }
}

class Typed extends CoqXMLTag {
  toString() { return "Typed"; }
}
