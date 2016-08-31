import { PpCmdBox, PpCmdPrint, PpCmdToken } from "../coq/ppcmd-token";
import { PpCmd, PpCmds, str } from "../printing/coq-pretty-printer";
import * as Pattern from "./pattern";
import { StrDef } from "../coq/str-token";

export function findPpCmdSuchThat(
  l: PpCmds,
  predicate: (_1: PpCmd) => boolean
): number {
  return _.findIndex(l, predicate);
}

export function ppCmdIsStringSuchThat(
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

export function ppCmdIsString(s: string): (_1: PpCmd) => boolean {
  return ppCmdIsStringSuchThat((s1) => s === s1.trim());
}

export function replacePpCmd(
  match: (_1: PpCmd) => boolean,
  replace: (_1: PpCmd) => PpCmds,
  l: PpCmds
): PpCmds {
  let pos = findPpCmdSuchThat(l, match);
  if (pos < 0) { return l; }
  return ([] as PpCmds).concat(
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
export function replaceToken(s1: string, s2: string, l: PpCmds): PpCmds {
  return replacePpCmd(
    ppCmdIsString(s1),
    (t: PpCmdPrint<StrDef>) => {
      return str(t.token.string.replace(s1, s2));
    },
    l
  );
}

function ppCmdsMatchGen(p: Pattern.Pattern[], l: PpCmds, o: Object): Maybe<Object> {
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

function ppCmdMatchGen(pat: Pattern.Pattern, p: PpCmd | any, o: Object): Maybe<Object> {
  if (pat instanceof Pattern.Anything) {
    return just(o);
  } else if (pat instanceof Pattern.ArrayPattern) {
    if (!(p instanceof Array)) { throw MatchFailure("ppCmdMatchGen > ArrayPattern", p); }
    return ppCmdsMatchGen(pat.array, p, o);
  } else if (pat instanceof Pattern.BinderPattern) {
    let binder = pat.binder;
    o[binder] = p;
    return just(o);
  } else if (pat instanceof Pattern.Constructor) {
    if (p instanceof pat.name) {
      return reduceMaybe(
        Object.keys(pat.fields),
        (acc, field) => {
          if (field in p) {
            return ppCmdMatchGen((<Pattern.Constructor>pat).fields[field], p[field], acc);
          } else {
            return nothing();
          }
        },
        o
      );
    } else {
      return nothing();
    }
  } else if (pat instanceof Pattern.StringPattern) {
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

function ppCmdsMatch(p: Pattern.Pattern[], l: PpCmds): Maybe<Object> {
  return ppCmdsMatchGen(p, l, {});
}

export function matchPattern(
  l: PpCmds,
  pat: Pattern.Pattern[],
  h: (_1: any) => PpCmds
): PpCmds {
  return ppCmdsMatch(pat, l).caseOf({
    nothing: () => l,
    just: (m) => h(m),
  });
}
