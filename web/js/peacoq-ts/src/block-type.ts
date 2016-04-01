import { PpCmdBox, PpCmds } from "./ppcmd-token";

export default BlockType;

export abstract class BlockType { }

class PpHBox extends BlockType {
  constructor(x: number) {
    super();
  }
}

class PpVBox extends BlockType {
  constructor(x: number) {
    super();
  }
}

class PpHVBox extends BlockType {
  constructor(x: number) {
    super();
  }
}

export class PpHoVBox extends BlockType {
  constructor(x: number) {
    super();
  }
}

class PpTBox extends BlockType { }

function h(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHBox(n), s)]; }
function v(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpVBox(n), s)]; }
function hv(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHVBox(n), s)]; }
function hov(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHoVBox(n), s)]; }
function t(s: PpCmds): PpCmds { return [new PpCmdBox(new PpTBox(), s)]; }
