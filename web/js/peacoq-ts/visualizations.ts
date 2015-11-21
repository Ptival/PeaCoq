
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
];

function patternAbs(l: PpCmds): PpCmds {
  if (l.length === 3) {
    let first = l[0];
    let arg = l[2];
    if (first instanceof PpCmdBox && first.contents.length === 1) {
      let second = first.contents[0];
      if (second instanceof PpCmdBox && second.contents.length === 7) {
        let printZ = second.contents[1];
        let printDot = second.contents[3];
        let printAbs = second.contents[5];
        if (printZ instanceof PpCmdPrint && printZ.token.string === "Z"
          && printDot instanceof PpCmdPrint && printDot.token.string === "."
          && printAbs instanceof PpCmdPrint && printAbs.token.string === "abs"
          ) {
          return [].concat(
            str("|"),
            l[2],
            str("|")
          );
        }
      }
    }
    return l;
  }
  return l;
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

// for "divides": \u2223
// for "does not divide": \u2224
function patternDivides(l: PpCmds): PpCmds {
  if (l.length !== 5) { return l; }
  let box1 = l[0];
  if (box1 instanceof PpCmdBox && box1.contents.length === 1) {
    let box2 = box1.contents[0];
    if (box2 instanceof PpCmdBox && box2.contents.length === 3) {
      let print = box2.contents[1];
      if (print instanceof PpCmdPrint && print.token.string === "divides") {
        return [].concat(
          [l[2]],
          [l[1]], // space
          str("\u2223"),
          [l[3]], // space
          [boxDropParentheses(l[4])]
          );
      }
    }
  }
  return l;
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
