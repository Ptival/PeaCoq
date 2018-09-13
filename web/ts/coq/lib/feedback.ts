import * as Loc from './loc'
import * as StateId from './stateid'
import * as SertopUtils from '../../sertop/utils'

export type Level
    = Debug
    | Info
    | Notice
    | Warning
    | Error

export class Debug  { private tag : 'Debug'   }
export class Error  { private tag : 'Error'   }
export class Info   { private tag : 'Info'    }
export class Notice { private tag : 'Notice'  }
export class Warning { private tag : 'Warning' }

namespace Level {

    export function create(s : string) : Level {
        switch (s) {
            case 'Debug'   : return new Debug()
            case 'Error'   : return new Error()
            case 'Info'    : return new Info()
            case 'Notice'  : return new Notice()
            case 'Warning' : return new Warning()
            default :
                debugger
                throw s
        }
    }

    export function isDebug  (l : Level) : l is Debug   { return l instanceof Debug   }
    export function isError  (l : Level) : l is Error   { return l instanceof Error   }
    export function isInfo   (l : Level) : l is Info    { return l instanceof Info    }
    export function isNotice (l : Level) : l is Notice  { return l instanceof Notice  }
    export function isWarning(l : Level) : l is Warning { return l instanceof Warning }

}

export type FeedbackContent
    = Processed
// | Incomplete
// | Complete
    | ProcessingIn
// | InProgress
    | WorkerStatus
    | AddedAxiom
// | GlobRef
// | GlobDef
    | FileDependency
    | FileLoaded
// | Custom
    | Message<Level>

export namespace FeedbackContent {
    export function isMessage  (fc : FeedbackContent) : fc is Message<Level> { return fc instanceof Message   }
    export function isProcessed(fc : FeedbackContent) : fc is Processed      { return fc instanceof Processed }

    export function isDebug  (fc : FeedbackContent) : fc is Message<Debug>   { return isMessage(fc) && fc.level instanceof Debug   }
    export function isError  (fc : FeedbackContent) : fc is Message<Error>   { return isMessage(fc) && fc.level instanceof Error   }
    export function isInfo   (fc : FeedbackContent) : fc is Message<Info >   { return isMessage(fc) && fc.level instanceof Info    }
    export function isNotice (fc : FeedbackContent) : fc is Message<Notice>  { return isMessage(fc) && fc.level instanceof Notice  }
    export function isWarning(fc : FeedbackContent) : fc is Message<Warning> { return isMessage(fc) && fc.level instanceof Warning }
}

export class AddedAxiom {
    private tag : 'AddedAxiom'
}

export class FileDependency {
    constructor(
        public dependsOnFile : Maybe<string>,
        public file : string
    ) { }
}

export class FileLoaded {
    constructor(
        qualifiedModuleName : string,
        path : string
    ) { }
}

export class Message<L extends Level> {
    constructor(
        public level : L,
        public location : Maybe<Loc.t>,
        public message : string
    ) { }
}

export class Processed {
    public toString() { return 'Processed' }
}

export class ProcessingIn {
    constructor(
        public branch : string
    ) { }
    public toString() {
        return `ProcessingIn(${this.branch})`
    }
}

export class WorkerStatus {
    public id : string
    public status : string
    constructor(c : [string, string]) {
        const [id, status] = c
        this.id = id
        this.status = status
    }
    public toString() {
        return `WorkerStatus(${this.id}, ${this.status})`
    }
}

export namespace FeedbackContent {

    export function fromSertop(o : any) : FeedbackContent {
        if (typeof o === 'string') {
            switch (o) {
                case 'AddedAxiom' : return new AddedAxiom()
                case 'Processed' : return new Processed()
                default : debugger
            }
        }
        const [name, ...args] = o
        switch (name) {
            case 'FileDependency' :
                const [depends, file] = args
                switch (depends.length) {
                    case 0 : return new FileDependency(nothing<string>(), file)
                    case 1 : return new FileDependency(just(depends[0]), file)
                    default :
                        debugger
                        throw 'FileDependency'
                }
            case 'FileLoaded' :
                const [qualifiedModuleName, path] = args
                return new FileLoaded(qualifiedModuleName, path)
            case 'Message' :
                const [level, maybeLocation, message] = args
                const location = (
                    maybeLocation.length === 0
                        ? nothing<Loc.t>()
                        : just(SertopUtils.coqLocationFromSexp(maybeLocation[0]))
                )
                return new Message(
                    Level.create(level),
                    location,
                    collectPpStrings(message)
                )
            case 'ProcessingIn' :
                const [branch] = args
                return new ProcessingIn(branch)
            default :
                debugger
                throw 'ProcessingIn'
        }
    }

}

function collectPCData(o : any) : string {
    if (typeof o === 'string') { return '' }
    if (
        typeof o === 'object' && o.length === 2
            && typeof o[0] === 'string' && o[0] === 'PCData'
    ) {
        return o[1]
    }
    return o.reduce((acc : string, elt : any) => `${acc}${collectPCData(elt)}`, '')
}

function collectPpStrings(o : any) : string {
    const [name, args] : [string, any] = o
    switch (name) {
        case 'Pp_glue'        : return args.reduce((acc : string, elt : any) => `${acc}${collectPpStrings(elt)}`, '')
        case 'Pp_print_break' : return '\n' // FIXME: there can be multiple breaks
        case 'Pp_string'      : return args
        default               : debugger; throw o
    }
}

export type DocId = number
export type RouteId = number

export class Feedback<C extends FeedbackContent> {
    constructor(
        public readonly docId : DocId,
        public readonly spanId : StateId.t,
        public readonly route : RouteId,
        public readonly contents : C,
    ) {
    }
    public toString() {
        return `Feedback(${this.docId}, ${this.spanId}, ${this.route}, ${this.contents})`
    }
}

export namespace Feedback {

    export function fromSertop(
        f : [any, [[string, string], [string, string], [string, string], [string, any[]]]]
    ) {
        const [, [ [, docId], [,spanId], [,route], [,contents] ]] = f
        return new Feedback(+ docId, + spanId, + route, FeedbackContent.fromSertop(contents))
    }

    export function isMessage  (f : Feedback<FeedbackContent>) : f is Feedback<Message<Level>> { return FeedbackContent.isMessage  (f.contents) }
    export function isProcessed(f : Feedback<FeedbackContent>) : f is Feedback<Processed>      { return FeedbackContent.isProcessed(f.contents) }

    export function isDebug  (f : Feedback<FeedbackContent>) : f is Feedback<Message<Debug>>   { return FeedbackContent.isDebug  (f.contents) }
    export function isError  (f : Feedback<FeedbackContent>) : f is Feedback<Message<Error>>   { return FeedbackContent.isError  (f.contents) }
    export function isInfo   (f : Feedback<FeedbackContent>) : f is Feedback<Message<Info >>   { return FeedbackContent.isInfo   (f.contents) }
    export function isNotice (f : Feedback<FeedbackContent>) : f is Feedback<Message<Notice>>  { return FeedbackContent.isNotice (f.contents) }
    export function isWarning(f : Feedback<FeedbackContent>) : f is Feedback<Message<Warning>> { return FeedbackContent.isWarning(f.contents) }

}
