
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
      str('<span style="vertical-align: sub;">'),
      t,
      str('</span>')
      ),
    l
    );
}

function patternForall(l: PpCmds): PpCmds {
  return replaceToken("forall", "∀", l);
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
  patternArrow,
  patternMult,
  patternScopeDelimiters,
  patternAnd,
  patternOr,
  patternEquiv,
];

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
