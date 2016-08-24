import { PpCmdBox, PpCmdPrint, PpCmdToken } from "../coq/ppcmd-token";
import { PpCmd, PpCmds, str } from "../printing/coq-pretty-printer";
import * as Pattern from "./pattern";
import { StrDef } from "../coq/str-token";
import { findPpCmdSuchThat, matchPattern, ppCmdIsString, ppCmdIsStringSuchThat, replacePpCmd, replaceToken } from "./utils";

let any = new Pattern.Anything();

function patternScopeDelimiters(l: PpCmds): PpCmds {
  return replacePpCmd(
    ppCmdIsStringSuchThat(s => s.startsWith("%")),
    t => [].concat(
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
    match => {
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

// for "divides": \u2223
// for "does not divide": \u2224
function patternDivides(l: PpCmds): PpCmds {
  return matchPattern(
    l,
    [
      box([box([any, tok("divides"), any])]),
      any, any, any, any
    ],
    match => {
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
    match => {
      return [].concat(
        [l[2]],
        str("²")
      );
    }
  );
}

let anything: any = undefined;

function box(contents: Pattern.Pattern[]): Pattern.Pattern {
  return new Pattern.Constructor(PpCmdBox, { contents: new Pattern.ArrayPattern(contents) });
}

function tok(s: string): Pattern.Pattern {
  return new Pattern.Constructor(PpCmdPrint, {
    token: new Pattern.Constructor(StrDef, { string: new Pattern.StringPattern(s) })
  });
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
    match => {
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
              box([new Pattern.BinderPattern("binder")]), // Binder binder
              any, //tok("\u00A0:"),
              any,
              box([new Pattern.BinderPattern("type")]) // Binder type
            ])
          ]),
          any,
          any,
          any,
          new Pattern.BinderPattern("body") // Binder body
        ])]),
        tok(")")
      ]),
      any,
      new Pattern.BinderPattern("upperBound")
    ],
    match => {
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
      new Pattern.BinderPattern("summand"),
      any,
      new Pattern.BinderPattern("upperBound")
    ],
    match => {
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

export let patterns: Array<(_1: PpCmds) => PpCmds> = [
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
