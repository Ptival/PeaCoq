import * as QueryCommand from './query-command'
import * as Sexp from './sexp'
import { escapeQuotes } from './utils'
import * as Feedback from '../coq/lib/feedback'
import * as StateId from '../coq/lib/stateid'

export type Cmd
    = Add
    | Cancel
    | Exec
    | Query
    // | Join
    // | Finish
    // and more...
    | Quit

export function isAdd   (c : Cmd) : c is Add    { return c instanceof Add    }
export function isCancel(c : Cmd) : c is Cancel { return c instanceof Cancel }
export function isExec  (c : Cmd) : c is Exec   { return c instanceof Exec   }
export function isQuery (c : Cmd) : c is Query  { return c instanceof Query  }
export function isQuit  (c : Cmd) : c is Quit   { return c instanceof Quit   }

export const cmdTagMinimum = 2 // 0 and 1 will be sent by the server
let cmdTagCounter : number = cmdTagMinimum

abstract class AbstractCommand {
    public tag : string
    constructor() { this.tag = (cmdTagCounter++).toString() }
    public abstract toSexp() : string
}

interface AddOptions {
    limit? : number
    ontop? : StateId.t
    newtip? : StateId.t
    verb? : boolean
}

export class Add extends AbstractCommand {
    constructor(
        public addOptions : AddOptions,
        public sentence : string,
        public readonly fromAutomation : boolean
    ) { super() }
    public toSexp() {
        const opts = ''.concat(
            Sexp.optionalToSexp('limit', this.addOptions.limit),
            Sexp.optionalToSexp('ontop', this.addOptions.ontop),
            Sexp.optionalToSexp('newtip', this.addOptions.newtip),
            Sexp.optionalToSexp('verb', this.addOptions.verb, b => b ? 'True' : 'False')
        )
        const o1 = Sexp.optionalToSexp('limit', this.addOptions.limit)
        // OLD STYLE
        // return `(StmAdd (${opts}) "${escapeQuotes(this.sentence)}")`
        return `(Add (${opts}) "${escapeQuotes(this.sentence)}")` // NEW STYLE
    }
}

export class Cancel extends AbstractCommand {
    constructor(
        public stateIds : StateId.t[]
    ) { super() }
    public toSexp() {
        const ids = this.stateIds.join(' ')
        // OLD STYLE
        // return `(StmCancel (${ids}))`
        return `(Cancel (${ids}))` // NEW STYLE
    }
}

export class Exec extends AbstractCommand {
    constructor(
        public stateId : StateId.t
    ) { super() }
    public toSexp() { return `(Exec ${this.stateId})` }
}

interface QueryOptions {
    // preds?: QueryPred[]
    // limit?: Maybe<number>
    sid?: StateId.t
    // pp?: PrintOptions
    route?: Feedback.RouteId
}

export class Query extends AbstractCommand {
    constructor(
        public queryOptions : QueryOptions,
        public query : QueryCommand.QueryCommand,
        public readonly fromAutomation : boolean
    ) { super() }
    public toSexp() {
        const opts = ''.concat(
            Sexp.optionalToSexp('route', this.queryOptions.route, (r : Feedback.RouteId) => r.toString()),
            Sexp.optionalToSexp('sid', this.queryOptions.sid, (s : StateId.t) => s.toString())
        )
        return `(Query (${opts}) ${this.query.toSexp()})`
    }
}

export class Quit extends AbstractCommand {
    public toSexp() {
        return 'Quit'
    }
}
