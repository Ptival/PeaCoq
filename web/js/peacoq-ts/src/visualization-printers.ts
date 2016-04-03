import { ppCmdsSameShape, PpCmd as PpCmdType, PpCmds } from "./coq-pretty-printer";
import * as PpCmd from "./coq/ppcmd-token";
import * as StrToken from "./coq/str-token";
import { patterns } from "./visualizations";

function htmlPrintStrToken(t: StrToken.StrToken): string {
  if (t instanceof StrToken.StrDef) {
    return (t.string);
  }
  if (t instanceof StrToken.StrLen) {
    return (t.string);
  }
  throw MatchFailure("htmlPrintStrToken", t);
}

function markDifferent(s: string): string {
  return '<span class="syntax peacoq-diff">' + s + '</span>';
}

function syntax(s) { return '<span class="syntax">' + s + '</span>'; }

function htmlPrintPpCmdDiff(p: PpCmdType, old: PpCmdType): string {
  if (p.constructor !== old.constructor) {
    return markDifferent(htmlPrintPpCmd(p));
  }
  if (p instanceof PpCmd.PpCmdPrint && old instanceof PpCmd.PpCmdPrint) {
    let res = htmlPrintStrToken(p.token);
    if (p.token.string !== old.token.string) { res = markDifferent(res); }
    return res;
  }
  if (p instanceof PpCmd.PpCmdBox && old instanceof PpCmd.PpCmdBox) {
    // FIXME: use blockType
    return syntax(htmlPrintPpCmdsDiff(p.contents, old.contents));
  }
  if (p instanceof PpCmd.PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmd.PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmd.PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmd.PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmd.PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmd.PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmd.PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmd.PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmd.PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmd.PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmd.PpCmdOpenTag) {
    return "<span class=tag-" + p.tag + ">";
  }
  if (p instanceof PpCmd.PpCmdCloseTag) {
    return "</span>";
  }
  throw MatchFailure("htmlPrintPpCmd", p);
}

export function htmlPrintPpCmd(p: PpCmdType): string {
  if (p instanceof PpCmd.PpCmdPrint) {
    return htmlPrintStrToken(p.token);
  }
  if (p instanceof PpCmd.PpCmdBox) {
    // FIXME: use blockType
    return syntax(htmlPrintPpCmds(p.contents));
  }
  if (p instanceof PpCmd.PpCmdPrintBreak) {
    return " ".repeat(p.nspaces);
  }
  if (p instanceof PpCmd.PpCmdSetTab) {
    return "TODO: PpCmdSetTab";
  }
  if (p instanceof PpCmd.PpCmdPrintTbreak) {
    return "TODO: PpCmdPrintTbreak";
  }
  if (p instanceof PpCmd.PpCmdWhiteSpace) {
    return "TODO: PpCmdWhiteSpace";
  }
  if (p instanceof PpCmd.PpCmdForceNewline) {
    return "TODO: PpCmdForceNewline";
  }
  if (p instanceof PpCmd.PpCmdPrintIfBroken) {
    return "TODO: PpCmdPrintIfBroken";
  }
  if (p instanceof PpCmd.PpCmdOpenBox) {
    return "TODO: PpCmdOpenBox";
  }
  if (p instanceof PpCmd.PpCmdCloseBox) {
    return "TODO: PpCmdCloseBox";
  }
  if (p instanceof PpCmd.PpCmdCloseTBox) {
    return "TODO: PpCmdCloseTBox";
  }
  if (p instanceof PpCmd.PpCmdComment) {
    return "TODO: PpCmdComment";
  }
  if (p instanceof PpCmd.PpCmdOpenTag) {
    return "<span class=tag-" + p.tag + ">";
  }
  if (p instanceof PpCmd.PpCmdCloseTag) {
    return "</span>";
  }
  throw MatchFailure("htmlPrintPpCmd", p);
}

export function htmlPrintPpCmds(l: PpCmds): string {
  _(patterns).each(function(pattern) {
    l = pattern(l);
  });
  return _.reduce(
    l,
    (acc: string, p: PpCmdType) => { return acc + htmlPrintPpCmd(p); },
    ""
  );
}

export function htmlPrintPpCmdsDiff(l: PpCmds, old: PpCmds): string {
  _(patterns).each(function(pattern) {
    l = pattern(l);
    old = pattern(old);
  });
  if (!ppCmdsSameShape(l, old)) {
    return markDifferent(
      _.reduce(
        l,
        (acc: string, p: PpCmdType) => {
          return acc + htmlPrintPpCmd(p);
        },
        ""
      )
    );
  }
  var z = _.zip(l, old);
  return _.reduce(
    z,
    (acc: string, [p, oldP]: [PpCmdType, PpCmdType]) => {
      return acc + htmlPrintPpCmdDiff(p, oldP);
    },
    ""
  );
}
