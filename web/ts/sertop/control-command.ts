import * as Sexp from './sexp'

function escapeQuotes(s : string) : string {
  return s.replace(/'/g, `\\'`)
}

interface AddOptions {
  limit? : number
  ontop? : StateId
  newtip? : StateId
  verb? : boolean
}

export class LibAdd implements ISertop.IControlCommand {
  constructor(
    public qualifiedPath : string[],
    public physicalPath : string,
    public containsML : boolean
  ) { }
  public toSexp() {
    const qPath = `'${this.qualifiedPath.join(`' '`)}'`
    return `(LibAdd (${qPath}) '${this.physicalPath}' ${Sexp.boolToSexp(this.containsML)})`
  }
}

export class StmAdd implements ISertop.IControlCommand {
  constructor(
    public addOptions : AddOptions,
    public sentence : string,
    public readonly fromAutomation : boolean
  ) { }
  public toSexp() {
    const opts = ''.concat(
      Sexp.optionalToSexp('limit', this.addOptions.limit),
      Sexp.optionalToSexp('ontop', this.addOptions.ontop),
      Sexp.optionalToSexp('newtip', this.addOptions.newtip),
      Sexp.optionalToSexp('verb', this.addOptions.verb, b => b ? 'True' : 'False')
    )
    const o1 = Sexp.optionalToSexp('limit', this.addOptions.limit)
    return `(StmAdd (${opts}) '${escapeQuotes(this.sentence)}')`
  }
}

export class StmCancel implements ISertop.IControlCommand.IStmCancel {
  constructor(
    public stateIds : StateId[]
  ) { }
  public toSexp() {
    const ids = this.stateIds.join(' ')
    return `(StmCancel (${ids}))`
  }
}

export class StmEditAt implements ISertop.IControlCommand {
  constructor(
    public stateId : StateId
  ) { }
  public toSexp() { return `(StmEditAt ${this.stateId})` }
}

// export class StmJoin implements Sertop.IControlCommand {
//   toSexp() { return 'StmJoin' }
// }

export class StmObserve implements ISertop.IControlCommand.IStmObserve {
  constructor(
    public stateId : StateId
  ) { }
  public toSexp() { return `(StmObserve ${this.stateId})` }
}

export class StmQuery implements ISertop.IControlCommand.IStmQuery {
  constructor(
    public queryOptions : ISertop.QueryOptions,
    public query : string,
    public readonly fromAutomation : boolean
  ) { }
  public toSexp() {
    const opts = ''.concat(
      Sexp.optionalToSexp('route', this.queryOptions.route, (r : RouteId) => r.toString()),
      Sexp.optionalToSexp('sid', this.queryOptions.sid, (s : StateId) => s.toString())
    )
    return `(StmQuery (${opts}) '${escapeQuotes(this.query)}')`
  }
}

export class StmState implements ISertop.IControlCommand {
  public toSexp() { return 'StmState' }
}

export class Quit implements ISertop.IControlCommand {
  public toSexp() { return 'Quit' }
}
