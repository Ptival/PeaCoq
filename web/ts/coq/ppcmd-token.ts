import { BlockType } from "./block-type"

export abstract class PpCmdToken<T> { }

export class PpCmdPrint<T> extends PpCmdToken<T> {
  constructor(public token: T) {
    super()
  }
}

export class PpCmdBox<T> extends PpCmdToken<T> {
  constructor(
    public blockType: BlockType,
    public contents: PpCmdToken<T>[]
  ) {
    super()
  }
}

export class PpCmdPrintBreak<T> extends PpCmdToken<T> {
  constructor(
    public nspaces: number,
    public offset: number
  ) {
    super()
  }
}

export class PpCmdSetTab<T> extends PpCmdToken<T> { }

export class PpCmdPrintTbreak<T> extends PpCmdToken<T> {
  constructor(x: number, y: number) {
    super()
  }
}

export class PpCmdWhiteSpace<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super()
  }
}

export class PpCmdForceNewline<T> extends PpCmdToken<T> { }

export class PpCmdPrintIfBroken<T> extends PpCmdToken<T> { }

export class PpCmdOpenBox<T> extends PpCmdToken<T> {
  constructor(public blockType: BlockType) { super() }
}

export class PpCmdCloseBox<T> extends PpCmdToken<T> { }

export class PpCmdCloseTBox<T> extends PpCmdToken<T> { }

export class PpCmdComment<T> extends PpCmdToken<T> {
  constructor(x: number) {
    super()
  }
}

export type Tag = string

export class PpCmdOpenTag<T> extends PpCmdToken<T> {
  constructor(public tag: Tag) { super() }
}

export class PpCmdCloseTag<T> extends PpCmdToken<T> { }
