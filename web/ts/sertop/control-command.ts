import { escapeQuotes } from './utils'
import * as Sexp from './sexp'

interface AddOptions {
    limit? : number
    ontop? : StateId
    newtip? : StateId
    verb? : boolean
}

// DEPRECATED
// export class LibAdd implements ISertop.IControlCommand {
//   constructor(
//     public qualifiedPath : string[],
//     public physicalPath : string,
//     public containsML : boolean
//   ) { }
//   public toSexp() {
//     const qPath = `'${this.qualifiedPath.join(`' '`)}'`
//     return `(LibAdd (${qPath}) '${this.physicalPath}' ${Sexp.boolToSexp(this.containsML)})`
//   }
// }

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
        // OLD STYLE
        // return `(StmAdd (${opts}) "${escapeQuotes(this.sentence)}")`
        return `(Add (${opts}) "${escapeQuotes(this.sentence)}")` // NEW STYLE
    }
}

export class StmCancel implements ISertop.IControlCommand.IStmCancel {
    constructor(
        public stateIds : StateId[]
    ) { }
    public toSexp() {
        const ids = this.stateIds.join(' ')
        // OLD STYLE
        // return `(StmCancel (${ids}))`
        return `(Cancel (${ids}))` // NEW STYLE
    }
}

// DEPRECATED?
// export class StmEditAt implements ISertop.IControlCommand {
//     constructor(
//         public stateId : StateId
//     ) { }
//     public toSexp() {
//         return `(StmEditAt ${this.stateId})`
//     }
// }

// export class StmJoin implements Sertop.IControlCommand {
//   toSexp() { return 'StmJoin' }
// }

export class Exec implements ISertop.IControlCommand.IStmExec {
    constructor(
        public stateId : StateId
    ) { }
    public toSexp() { return `(Exec ${this.stateId})` }
}

// DEPRECATED? See: Join / Finish?
// export class StmObserve implements ISertop.IControlCommand.IStmObserve {
//     constructor(
//         public stateId : StateId
//     ) { }
//     public toSexp() { return `(StmObserve ${this.stateId})` }
// }

export class StmQuery implements ISertop.IControlCommand.IStmQuery {
    constructor(
        public queryOptions : ISertop.QueryOptions,
        public query : ISertop.IQueryCommand,
        public readonly fromAutomation : boolean
    ) { }
    public toSexp() {
        const opts = ''.concat(
            Sexp.optionalToSexp('route', this.queryOptions.route, (r : RouteId) => r.toString()),
            Sexp.optionalToSexp('sid', this.queryOptions.sid, (s : StateId) => s.toString())
        )
        // OLD STYLE
        // return `(StmQuery (${opts}) "${escapeQuotes(this.query)}")`
        return `(Query (${opts}) ${this.query.toSexp()})`
    }
}

// DEPRECATED?
export class StmState implements ISertop.IControlCommand {
    public toSexp() {
        return 'StmState'
    }
}

export class Quit implements ISertop.IControlCommand {
    public toSexp() {
        // OLD STYLE
        // return 'StmQuit'
        return 'Quit' // NEW STYLE
    }
}
