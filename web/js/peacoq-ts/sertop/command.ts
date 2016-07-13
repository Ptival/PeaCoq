import * as ControlCommand from "./control-command";
import * as Sexp from "./sexp";

export const cmdTagMinimum = 2;
let cmdTagCounter = cmdTagMinimum;

abstract class Command implements ISertop.ICommand {
  public tag: CommandTag;
  constructor() { this.tag = (cmdTagCounter++).toString(); }
  abstract toSexp(): string;
}

export class Control<C extends ISertop.IControlCommand> extends Command implements ISertop.IControl<C> {
  constructor(
    public controlCommand: C
  ) { super(); }
  toSexp() { return `(Control ${this.controlCommand.toSexp()})`; }
}

export class Query<Q extends ISertop.IQueryCommand> extends Command implements ISertop.IQuery<Q> {
  constructor(
    public queryOptions: ISertop.QueryOptions,
    public queryCommand: Q
  ) { super(); }
  toSexp() {
    const opts = "".concat(
      // Sexp.optionalToSexp("limit", this.queryOptions.limit),
      // Sexp.optionalToSexp("ontop", this.queryOptions.ontop),
      // Sexp.optionalToSexp("newtip", this.queryOptions.newtip),
      // Sexp.optionalToSexp("verb", this.queryOptions.verb, b => b ? "True" : "False")
    );
    return `(Query (${opts}) ${this.queryCommand.toSexp()})`;
  }
}
