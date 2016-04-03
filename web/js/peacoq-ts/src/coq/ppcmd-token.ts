import BlockType from "./block-type";

export abstract class PpCmdToken<T> { }

export class PpCmdPrint<T> extends PpCmdToken<T> {
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

export class PpCmdPrintBreak<T> extends PpCmdToken<T> {
  nspaces: number;
  offset: number;
  constructor(x: number, y: number) {
    super();
    this.nspaces = x;
    this.offset = y;
  }
}

export class PpCmdSetTab<T> extends PpCmdToken<T> { }

export class PpCmdPrintTbreak<T> extends PpCmdToken<T> {
  constructor(x: number, y: number) {
    super();
  }
}

export class PpCmdWhiteSpace<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super();
  }
}

export class PpCmdForceNewline<T> extends PpCmdToken<T> { }

export class PpCmdPrintIfBroken<T> extends PpCmdToken<T> { }

export class PpCmdOpenBox<T> extends PpCmdToken<T> {
  blockType: BlockType;
  constructor(b: BlockType) {
    super();
    this.blockType = b;
  }
}

export class PpCmdCloseBox<T> extends PpCmdToken<T> { }

export class PpCmdCloseTBox<T> extends PpCmdToken<T> { }

export class PpCmdComment<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super();
  }
}

export type Tag = string;

export class PpCmdOpenTag<T> extends PpCmdToken<T> {
  tag: string;
  constructor(t: Tag) {
    super();
    this.tag = t;
  }
}

export class PpCmdCloseTag<T> extends PpCmdToken<T> { }
