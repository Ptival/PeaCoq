import * as ControlCommand from "./control-command";

export type Command = Control

let cmdTagCounter = 0;

abstract class Cmd implements Sertop.ICmd {
  public tag: number;
  constructor() { this.tag = cmdTagCounter++; }
  abstract toSexp(): string;
}

export class Control extends Cmd implements Sertop.ICmd {
  constructor(
    public controlCommand: ControlCommand.ControlCommand
  ) { super(); }
  toSexp() { return `(Control ${this.controlCommand.toSexp()})`; }
}
