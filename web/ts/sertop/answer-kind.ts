import * as Exception from './exception'
import * as Loc from '../coq/lib/loc'
import * as Tip from '../coq/tip'
import * as SertopUtils from './utils'

export class Ack implements ISertop.IAck { }

export class Completed implements ISertop.ICompleted { }

export class CoqExn implements ISertop.ICoqExn {
    constructor(
        public exn : IException
    ) { }
    public getMessage() : string { return this.exn.getMessage() }
}

export class ObjList implements ISertop.IObjList {
    constructor(
        public readonly objects : any[]
    ) { }
}

export class StmAdded implements ISertop.IStmAdded {
    constructor(
        public stateId : StateId,
        public location : Loc.t,
        public tip : Tip.NewTip | Tip.Unfocus
    ) {
        // console.log('StmAdded', stateId)
    }
}

export class StmCanceled implements ISertop.IStmCanceled {
    constructor(
        public stateIds : StateId[]
    ) { }
}

export class StmCurId implements ISertop.IStmCurId {
    constructor(
        public curId : number
    ) { }
}

export class StmEdited implements ISertop.IStmEdited {
    constructor(
        public tip : Tip.NewTip // | Focus
    ) { }
}

export function create(o : any) : ISertop.IAnswerKind {
    if (typeof o === 'string') {
        switch (o) {
            case 'Ack' : return new Ack()
            case 'Completed' : return new Completed()
            default : debugger
        }
    }
    const [kind, ...args] = o
    switch (kind) {

        case 'CoqExn' :
            return new CoqExn(Exception.create(args))

        case 'Added' : { // opening a scope prevents hoisted variable clashes
            const [stateId, coqLocation, tip] : [string, string, string] = args
            return new StmAdded(+ stateId, SertopUtils.coqLocationFromSexp(coqLocation), tip)
        }

        case 'ObjList' : {
            const [objects] : any[] = args
            return new ObjList(args)
        }

        case 'StmCurId' :
            const [curId] = args
            return new StmCurId(curId)

        case 'StmEdited' :
            const [tip] = args
            if (tip === 'NewTip') {
                return new StmEdited(new Tip.NewTip())
            } else {
                debugger
                throw 'StmEdited'
            }

        case 'Canceled' :
            const [stateIds] : string[][] = args
            return new StmCanceled(stateIds.map(s => + s))

        default :
            debugger
            throw 'AnswerKind.create'
    }
}
