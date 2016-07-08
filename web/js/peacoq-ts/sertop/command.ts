import * as ControlCommand from "./control-command";
import * as Sexp from "./sexp";

let cmdTagCounter = 0;

interface QueryOptions {
  // preds?: QueryPred[];
  // limit?: Maybe<number>;
  // sid?: StateId;
  // pp?: PrintOptions;
}

abstract class Command implements ISertop.ICommand {
  public tag: number;
  constructor() { this.tag = cmdTagCounter++; }
  abstract toSexp(): string;
}

export class Control<C extends ISertop.IControlCommand> extends Command implements ISertop.ICommand {
  constructor(
    public controlCommand: C
  ) { super(); }
  toSexp() { return `(Control ${this.controlCommand.toSexp()})`; }
}

export class Query<Q extends ISertop.IQueryCommand> extends Command implements ISertop.ICommand {
  constructor(
    public queryOptions: QueryOptions,
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
