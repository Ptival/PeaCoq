import * as Exception from './exception'
import * as Loc from '../coq/lib/loc'
import * as Tip from '../coq/tip'
import * as SertopUtils from './utils'
import * as StateId from '../coq/lib/stateid'

export type AnswerKind
    = Ack
    | Completed
    | Added
    | Canceled
    | ObjList
    | CoqExn

export function isAck      (ak : AnswerKind) : ak is Ack       { return ak instanceof Ack       }
export function isCompleted(ak : AnswerKind) : ak is Completed { return ak instanceof Completed }
export function isAdded    (ak : AnswerKind) : ak is Added     { return ak instanceof Added     }
export function isCanceled (ak : AnswerKind) : ak is Canceled  { return ak instanceof Canceled  }
export function isObjList  (ak : AnswerKind) : ak is ObjList   { return ak instanceof ObjList   }
export function isCoqExn   (ak : AnswerKind) : ak is CoqExn    { return ak instanceof CoqExn    }

export class Ack {
    private tag : 'Ack'
}

export class Completed {
    private tag : 'Completed'
}

export class Added {
    constructor(
        public stateId : StateId.t,
        public location : Loc.t,
        public tip : Tip.NewTip | Tip.Unfocus
    ) { }
}

export class Canceled {
    constructor(
        public stateIds : StateId.t[]
    ) { }
}

export class ObjList {
    constructor(
        public readonly objects : any[]
    ) { }
}

export class CoqExn {
    constructor(
        public exn : Exception.Exception
    ) { }
    public getMessage() : string { return this.exn.getMessage() }
}

export function create(o : any) : AnswerKind {
    if (typeof o === 'string') {
        switch (o) {
            case 'Ack' : return new Ack()
            case 'Completed' : return new Completed()
            default : debugger
        }
    }
    const [kind, ...args] = o
    switch (kind) {

        case 'Ack' : return new Ack()

        case 'Completed' : return new Completed()

        case 'Added' : { // opening a scope prevents hoisted variable clashes
            const [stateId, coqLocation, tip] : [string, [string, string][], string] = args
            if (typeof tip !== 'string') {
                debugger // This should be the case for Unfocus, figure it out
            }
            return new Added(+ stateId, SertopUtils.coqLocationFromSexp(coqLocation), Tip.parseNewTipOrUnfocus(tip))
        }

        case 'Canceled' :
            const stateIds : string[] = args
            return new Canceled(stateIds.map(s => + s))

        case 'ObjList' : {
            const [objects] : any[] = args
            return new ObjList(args)
        }

        case 'CoqExn' :
            return new CoqExn(Exception.create(args))

        default :
            debugger
            throw 'AnswerKind.create'
    }
}
