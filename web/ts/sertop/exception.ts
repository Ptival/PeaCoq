import * as PeaCoqUtils from '../peacoq/utils'

export type Exception
    = EvaluatedError
    | NoCurrentProof
    | UserError

class EvaluatedError {
    constructor(
        public message : any,
        public exception : Maybe<any>
    ) { }
    public getMessage() { return this.message }
}

class NoCurrentProof {
    public getMessage() { return 'No current proof.' }
}

class UserError {
    constructor(
        public e : any,
        public message : any
    ) { }
    public getMessage() { return 'TODO : UserError' }
}

/*
  Listing shapes supported so far :
  [['Anomaly : ...']]
*/
export function create(args : any) : Exception {
    if (typeof args === 'string') {
        switch (args) {
                // case 'NoCurrentProof' : return new NoCurrentProof()
            default : debugger
        }
    }
    switch (args.length) {
        case 1 :
            const [error] = args[0]
            debugger
            throw error
        case 3 : {
            // Case : [..., ..., ['ExplainErr.EvaluatedError', '...']]
            if (args[2][0] === 'ExplainErr.EvaluatedError') {
                debugger
                throw error
            }
            return PeaCoqUtils.thisShouldNotHappen()
        }
        default : debugger
    }
    // const [[kind, ...o]] = args
    // if (o[0] === undefined) { debugger }
    // switch (kind) {
    //   case 'Cerrors.EvaluatedError' :
    //     switch (o.length) {
    //       case 1 : return new EvaluatedError(o[0], nothing())
    //       case 2 : return new EvaluatedError(o[0], just(o[1]))
    //       default : debugger
    //     }
    //   case 'Errors.UserError' :
    //     return new UserError(o[0][0], o[0][1])
    //   default :
    //   switch (o.length) {
    //     case 0 : return new Exception(o[0])
    //     default : debugger
    //   }
    // }
    debugger
    throw 'TODO'
}
