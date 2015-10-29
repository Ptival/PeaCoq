
/* Visualization for: forall x, ...
0: OpenTag("keyword")
1: forall
2: CloseTag
...
*/
function patternForall(l: PpCmds): PpCmds {
  if (l.length > 3) {
    let p = l[1];
    if (p instanceof PpCmdPrint) {
      let token = p.token;
      if (token.string === "forall") {
        return [].concat(
          [l[0]],
          str("∀"),
          [l[2]],
          l.slice(3)
        );
      }
    }
  }
  return l;
}

function patternPlus(l: PpCmds): PpCmds {
  if (l.length === 4) {
    let plusSign = l[1];
    if (plusSign instanceof PpCmdPrint) {
      let token = plusSign.token;
      if (token instanceof StrDef) {
        if (token.string === "\u00A0+") {
          return [].concat(
            [l[0]],
            str(" + "),
            [l[2], l[3]]
            );
        }
      }
    }
  }
  return l;
}

/* Visualization for: x ^ y
0: OpenTag("variable")
1: x
2: CloseTag("variable")
3: Break
4: OpenTag("notation")
5: ^
6: CloseTag
7: y
*/
function patternPow(l: PpCmds): PpCmds {
  let signPosition = 5;
  if (l.length === 8) {
    let powSign = l[signPosition];
    if (powSign instanceof PpCmdPrint) {
      let token = powSign.token;
      if (token instanceof StrDef) {
        if (token.string === "^\u00A0") {
          return [].concat(
            l.slice(0, 3),
            str('<span style="vertical-align: super;">'),
            l.slice(7),
            str('</span>')
            );
        }
      }
    }
  }
  return l;
}
