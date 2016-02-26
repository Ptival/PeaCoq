
function findPpCmdSuchThat(
  l: PpCmds,
  predicate: (_1: PpCmd) => boolean
): number {
  return _.findIndex(l, predicate);
}

function ppCmdIsStringSuchThat(
  predicate: (_1: string) => boolean
): (_1: PpCmd) => boolean {
  return (token: PpCmd) => {
    return (
      token instanceof PpCmdPrint
      && token.token instanceof StrDef
      && predicate(token.token.string)
    );
  }
}

function ppCmdIsString(s: string): (_1: PpCmd) => boolean {
  return ppCmdIsStringSuchThat((s1) => s === s1.trim());
}

function replacePpCmd(
  match: (_1: PpCmd) => boolean,
  replace: (_1: PpCmd) => PpCmds,
  l: PpCmds
): PpCmds {
  let pos = findPpCmdSuchThat(l, match);
  if (pos < 0) { return l; }
  return [].concat(
    l.slice(0, pos),
    replace(l[pos]),
    l.slice(pos + 1)
  );
}

/*
In practice the tokens come with their spacing incorporated, which is
sometimes \u00A0<token> or sometimes <token>\u00A0, so we perform the
replacement with a regexp to preserve the \u00A0.
*/
function replaceToken(s1: string, s2: string, l: PpCmds): PpCmds {
  return replacePpCmd(
    ppCmdIsString(s1),
    (t: PpCmdPrint<StrDef>) => {
      return str(t.token.string.replace(s1, s2));
    },
    l
  );
}

function patternScopeDelimiters(l: PpCmds): PpCmds {
  return replacePpCmd(
    ppCmdIsStringSuchThat((s) => s.startsWith("%")),
    (t) => [].concat(
      str('<span style="vertical-align: sub; color: #9C27B0; font-size: xx-small;">'),
      str((<any>t).token.string.replace("%", "")),
      str('</span>')
    ),
    l
  );
}

function patternForall(l: PpCmds): PpCmds {
  return replaceToken("forall", "∀", l);
}

function patternExists(l: PpCmds): PpCmds {
  return replaceToken("exists", "∃", l);
}

function patternArrow(l: PpCmds): PpCmds {
  return replaceToken("->", "→", l);
}

function patternMult(l: PpCmds): PpCmds {
  return replaceToken("*", "×", l);
}

function patternAnd(l: PpCmds): PpCmds {
  return replaceToken("/\\", "∧", l);
}

function patternOr(l: PpCmds): PpCmds {
  return replaceToken("\\/", "∨", l);
}

function patternEquiv(l: PpCmds): PpCmds {
  return replaceToken("<->", "⇔", l);
}

function patternNat(l: PpCmds): PpCmds {
  return replaceToken("nat", "\u2115", l);
}

function patternZ(l: PpCmds): PpCmds {
  return replaceToken("Z", "\u2124", l);
}

let patterns: Array<(_1: PpCmds) => PpCmds> = [
  patternPow,
  patternForall,
  patternExists,
  patternArrow,
  patternMult,
  patternScopeDelimiters,
  patternAnd,
  patternOr,
  patternEquiv,
  patternDivides,
  patternAbs,
  patternZSquare,
  patternZOfNat,
  patternSumLambda,
  patternSum, // keep this one after patternSumLambda as it is less general
  patternNat,
  patternZ,
];

function patternAbs(l: PpCmds): PpCmds {
  return matchPattern(
    l,
    [
      box([
        box([
          any, tok("Z"), any, tok("."), any, tok("abs")
        ])
      ]),
      any,
      any
    ],
    (match) => {
      return [].concat(
        str("|"),
        l[2],
        str("|")
      );
    }
  );
}

/* Visualization for: x ^ y
...
OpenTag("notation")
"^ "
CloseTag
...
*/
function patternPow(l: PpCmds): PpCmds {
  let pos = findPpCmdSuchThat(l, ppCmdIsString("^"));
  if (pos > 0) {
    return [].concat(
      l.slice(0, pos - 2),
      str('<span style="vertical-align: super;">'),
      l.slice(pos + 2),
      str('</span>')
    );
  }
  return l;
}

function matchPattern(
  l: PpCmds,
  pat: Pattern[],
  h: (_1: any) => PpCmds
): PpCmds {
  return ppCmdsMatch(pat, l).caseOf({
    nothing: () => l,
    just: (m) => h(m),
  });
}

// for "divides": \u2223
// for "does not divide": \u2224
function patternDivides(l: PpCmds): PpCmds {
  return matchPattern(
    l,
    [
      box([box([any, tok("divides"), any])]),
      any, any, any, any
    ],
    (match) => {
      return [].concat(
        [l[2]],
        [l[1]], // space
        str("\u2223"),
        [l[3]], // space
        [boxDropParentheses(l[4])]
      );
    }
  );
}

function patternZSquare(l: PpCmds): PpCmds {
  return matchPattern(l,
    [
      box([
        box([
          any, tok("Z"), any, tok("."), any, tok("square"), any
        ])
      ]),
      any, any
    ],
    (match) => {
      return [].concat(
        [l[2]],
        str("²")
      );
    }
  );
}

let anything: any = undefined;

class Pattern { }

class Anything extends Pattern { }

class ArrayPattern extends Pattern {
  array: Pattern[];
  constructor(a: Pattern[]) { super(); this.array = a; }
}

class BinderPattern extends Pattern {
  binder: string;
  constructor(name: string) { super(); this.binder = name; }
}

class Constructor extends Pattern {
  name: Function;
  fields: Object;
  constructor(name: Function, fields: Object) {
    super();
    this.name = name;
    this.fields = fields;
  }
}

class StringPattern extends Pattern {
  string: string;
  constructor(s: string) { super(); this.string = s; }
}

function box(contents: Pattern[]): Pattern {
  return new Constructor(PpCmdBox, { contents: new ArrayPattern(contents) });
}

function tok(s: string): Pattern {
  return new Constructor(PpCmdPrint, {
    token: new Constructor(StrDef, { string: new StringPattern(s) })
  });
}

let any: Pattern = new Anything();

function ppCmdsMatchGen(p: Pattern[], l: PpCmds, o: Object): Maybe<Object> {
  if (p.length !== l.length) { return nothing(); }
  let zip = _.zip(p, l);
  for (let index in zip) {
    let [pat, cmd] = zip[index];
    let shortCircuit = ppCmdMatchGen(pat, cmd, o).caseOf({
        nothing: () => true,
        just: (newo) => { o = newo; return false; }
    });
    if (shortCircuit) { return nothing(); }
  }
  return just(o);
}

function reduceMaybe<IN, ACC>(
  a: Array<IN>,
  f: (_1: ACC, _2: IN) => Maybe<ACC>,
  acc: ACC
): Maybe<ACC> {
  return _.reduce(
    a,
    (acc: Maybe<ACC>, elt: IN) => {
      return acc.caseOf({
        nothing: () => acc,
        just: (acc) => f (acc, elt),
      });
    },
    just(acc)
  );
}

function ppCmdMatchGen(pat: Pattern, p: PpCmd | any, o: Object): Maybe<Object> {
  if (pat instanceof Anything) {
    return just(o);
  } else if (pat instanceof ArrayPattern) {
    if (!(p instanceof Array)) { throw MatchFailure("ppCmdMatchGen > ArrayPattern", p); }
    return ppCmdsMatchGen(pat.array, p, o);
  } else if (pat instanceof BinderPattern) {
    let binder = pat.binder;
    o[binder] = p;
    return just(o);
  } else if (pat instanceof Constructor) {
    if (p instanceof pat.name) {
      return reduceMaybe(
        Object.keys(pat.fields),
        (acc, field) => {
          if (field in p) {
            return ppCmdMatchGen(pat.fields[field], p[field], acc);
          } else {
            return nothing();
          }
        },
        o
      );
    } else {
      return nothing();
    }
  } else if (pat instanceof StringPattern) {
    if (!(typeof p === "string")) {
      throw MatchFailure("ppCmdMatchGen > StringPattern", p);
    }
    if (pat.string === p) {
      return just(o);
    } else {
      return nothing();
    }
  } else {
    throw MatchFailure("patternMatch > rec", pat);
  }
}

function ppCmdsMatch(p: Pattern[], l: PpCmds): Maybe<Object> {
  return ppCmdsMatchGen(p, l, {});
}

function patternZOfNat(l: PpCmds): PpCmds {
  return matchPattern(l,
    // TODO: we could have a pattern like this one removing outer parentheses
    [
      box([
        box([any, tok("Z"), any, any, any, tok("of_nat"), any])
      ]),
      any,
      any
    ],
    (match) => {
      return [].concat(
        [l[2]],
        str('<span style="vertical-align: sub; font-size: xx-small;">'),
        str("\u2115"),
        str('</span>')
      );
    }
  );
}

function boxDropParentheses(p: PpCmd): PpCmd {
  if (p instanceof PpCmdBox && p.contents.length === 3) {
    let open = p.contents[0];
    let close = p.contents[2];
    if (open instanceof PpCmdPrint && open.token.string === "("
      && close instanceof PpCmdPrint && close.token.string === ")")
      return p.contents[1];
  }
  return p;
}

function patternSumLambda(l: PpCmds): PpCmds {
  return matchPattern(
    l,
    [
      box([box([any, tok("sum"), any])]),
      any,
      box([
        tok("("),
        box([box([
          box([
            any,
            tok("fun"),
            any,
            any,
            box([
              box([new BinderPattern("binder")]), // Binder binder
              any, //tok("\u00A0:"),
              any,
              box([new BinderPattern("type")]) // Binder type
            ])
          ]),
          any,
          any,
          any,
          new BinderPattern("body") // Binder body
        ])]),
        tok(")")
      ]),
      any,
      new BinderPattern("upperBound")
    ],
    (match) => {
      return [].concat(
        str('<span style="display: flex; flex-flow: row; align-items: center;">'),
        str('<span style="font-family: MathJax_Size4; font-size:120%;">(</span>'),
        str('<span style="display: flex; flex-flow: column; margin-right: 0.5em;">'),
        str('<span style="display: flex; flex-flow: row; justify-content: center;">'),
        str('<span>'),
        boxDropParentheses(match.upperBound),
        str('</span></span>'),
        str('<span style="display:flex; flex-flow: row; justify-content: center; font-family: MathJax_Size2; font-size: 120%;">∑</span>'),
        str('<span style="display: flex; flex-flow: row; justify-content: center;">'),
        str('<span>'),
        match.binder,
        str(' = 0'),
        str('</span></span></span>'),
        str('<span><span>'),
        match.body,
        str('</span>'),
        str('</span><span style="font-family: MathJax_Size4; font-size:120%;">)</span></span>')
      );
    }
  );
}

function patternSum(l: PpCmds): PpCmds {
  return matchPattern(
    l,
    [
      box([box([any, tok("sum"), any])]),
      any,
      new BinderPattern("summand"),
      any,
      new BinderPattern("upperBound")
    ],
    (match) => {
      return [].concat(
        str('<span style="display: flex; flex-flow: row; align-items: center;">'),
        str('<span style="font-family: MathJax_Size4; font-size:120%;">(</span>'),
        str('<span style="display: flex; flex-flow: column; margin-right: 0.5em;">'),
        str('<span style="display: flex; flex-flow: row; justify-content: center;">'),
        str('<span>'),
        boxDropParentheses(match.upperBound),
        str('</span></span>'),
        str('<span style="display:flex; flex-flow: row; justify-content: center; font-family: MathJax_Size2; font-size: 120%;">∑</span>'),
        str('<span style="display: flex; flex-flow: row; justify-content: center;">'),
        str('<span>0</span></span></span>'),
        str('<span><span>'),
        match.summand,
        str('</span>'),
        str('</span><span style="font-family: MathJax_Size4; font-size:120%;">)</span></span>')
      );
    }
  );
}
