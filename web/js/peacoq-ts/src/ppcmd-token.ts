import BlockType from "./block-type";

abstract class PpCmdToken<T> { }

class PpCmdPrint<T> extends PpCmdToken<T> {
  token: T;
  constructor(t: T) {
    super();
    this.token = t;
  }
}

export class PpCmdBox<T> extends PpCmdToken<T> {
  blockType: BlockType;
  contents: PpCmdToken<T>[];
  constructor(b: BlockType, x: PpCmdToken<T>[]) {
    super();
    this.blockType = b;
    this.contents = x;
  }
}

class PpCmdPrintBreak<T> extends PpCmdToken<T> {
  nspaces: number;
  offset: number;
  constructor(x: number, y: number) {
    super();
    this.nspaces = x;
    this.offset = y;
  }
}

class PpCmdSetTab<T> extends PpCmdToken<T> { }

class PpCmdPrintTbreak<T> extends PpCmdToken<T> {
  constructor(x: number, y: number) {
    super();
  }
}

class PpCmdWhiteSpace<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super();
  }
}

class PpCmdForceNewline<T> extends PpCmdToken<T> { }

class PpCmdPrintIfBroken<T> extends PpCmdToken<T> { }

class PpCmdOpenBox<T> extends PpCmdToken<T> {
  blockType: BlockType;
  constructor(b: BlockType) {
    super();
    this.blockType = b;
  }
}

class PpCmdCloseBox<T> extends PpCmdToken<T> { }

class PpCmdCloseTBox<T> extends PpCmdToken<T> { }

class PpCmdComment<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super();
  }
}

export type Tag = string;

class PpCmdOpenTag<T> extends PpCmdToken<T> {
  tag: string;
  constructor(t: Tag) {
    super();
    this.tag = t;
  }
}

class PpCmdCloseTag<T> extends PpCmdToken<T> { }

type PpCmd = PpCmdToken<StrToken>;
export type PpCmds = PpCmd[];

function cut(): PpCmds { return [new PpCmdPrintBreak(0, 0)]; }

export function mt(): PpCmds { return []; }

function spc(): PpCmds { return [new PpCmdPrintBreak(1, 0)]; }

export function str(s: string): PpCmds { return [new PpCmdPrint(new StrDef(s))]; }

function surround(p: PpCmds): PpCmds {
  return hov(1, [].concat(str("("), p, str(")")));
}

function openTag(t: Tag): PpCmds { return [new PpCmdOpenTag(t)]; }
function closeTag(t: Tag): PpCmds { return [new PpCmdCloseTag()]; }
function tag(t: Tag, s: PpCmds): PpCmds {
  return [].concat(openTag(t), s, closeTag(t));
}

function tagEvar(p: PpCmds): PpCmds { return tag("evar", p); }
function tagKeyword(p: PpCmds): PpCmds { return tag("keyword", p); }
function tagNotation(r: PpCmds): PpCmds { return tag("notation", r); }
function tagPath(p: PpCmds): PpCmds { return tag("path", p); }
function tagRef(r: PpCmds): PpCmds { return tag("reference", r); }
function tagType(r: PpCmds): PpCmds { return tag("univ", r); }
function tagVariable(p: PpCmds): PpCmds { return tag("variable", p); }

function isMt(p: PpCmds): boolean {
  return (p.length === 0);
}

/*
peaCoqBox should not disrupt the pretty-printing flow, but add a
<span> so that sub-expression highlighting is more accurate
*/
function peaCoqBox(l: PpCmds): PpCmds {
  return [new PpCmdBox(new PpHoVBox(0), l)];
}
function tagUnparsing(unp: Unparsing, pp1: PpCmds): PpCmds {
  if (unp instanceof UnpTerminal) {
    return tagNotation(pp1);
  }
  return pp1;
}





function PpCmdOfCut(c: PpCut): PpCmds {
  if (c instanceof PpTab) { return tab(); }
  if (c instanceof PpFnl) { return fnl(); }
  if (c instanceof PpBrk) { return brk(c.n1, c.n2); }
  if (c instanceof PpTbrk) { return tbrk(c.n1, c.n2); }
  throw MatchFailure("PpCmdOfCut", c);
}
