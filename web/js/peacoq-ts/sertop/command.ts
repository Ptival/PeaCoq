import * as ControlCommand from "./control-command";

export type Command = Control<ISertop.IControlCommand>

let cmdTagCounter = 0;

abstract class Cmd implements ISertop.ICmd {
  public tag: number;
  constructor() { this.tag = cmdTagCounter++; }
  abstract toSexp(): string;
}

export class Control<C extends ISertop.IControlCommand> extends Cmd implements ISertop.ICmd {
  constructor(
    public controlCommand: C
  ) { super(); }
  toSexp() { return `(Control ${this.controlCommand.toSexp()})`; }
}
