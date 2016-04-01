import { h, hov, hv, PpCmds, t, v } from "./ppcmd-token";

export abstract class PpBox { }

class PpHB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpHoVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpHVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpVB extends PpBox {
  n: number;
  constructor(n: number) { super(); this.n = n; }
}

class PpTB extends PpBox { }

function h(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHBox(n), s)]; }
function v(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpVBox(n), s)]; }
function hv(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHVBox(n), s)]; }
function hov(n: number, s: PpCmds): PpCmds { return [new PpCmdBox(new PpHoVBox(n), s)]; }
function t(s: PpCmds): PpCmds { return [new PpCmdBox(new PpTBox(), s)]; }

function PpCmdOfBox(b: PpBox, s: PpCmds): PpCmds {
  if (b instanceof PpHB) { return h(b.n, s); }
  if (b instanceof PpHoVB) { return hov(b.n, s); }
  if (b instanceof PpHVB) { return hv(b.n, s); }
  if (b instanceof PpVB) { return v(b.n, s); }
  if (b instanceof PpTB) { return t(s); }
  throw MatchFailure("PpCmdOfBox", b);
}
