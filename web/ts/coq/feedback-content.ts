import * as MessageLevel from './message-level'
import * as SertopUtils from '../sertop/utils'

export function fromSertop(o : any) : IFeedbackContent {
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
                    ? nothing<CoqLocation>()
                    : just(SertopUtils.coqLocationFromSexp(maybeLocation[0]))
            )
            return new Message(
                MessageLevel.create(level),
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

export class AddedAxiom implements IFeedbackContent.IAddedAxiom { }

export class FileDependency implements IFeedbackContent.IFileDependency {
    constructor(
        public dependsOnFile : Maybe<string>,
        public file : string
    ) { }
}

export class FileLoaded implements IFeedbackContent.IFileLoaded {
    constructor(
        qualifiedModuleName : string,
        path : string
    ) { }
}

export class Message<L extends IMessageLevel> implements IFeedbackContent.IMessage<L> {
    constructor(
        public level : L,
        public location : Maybe<CoqLocation>,
        public message : string
    ) { }
}

export class Processed implements IFeedbackContent.IProcessed {
    public toString() { return 'Processed' }
}

export class ProcessingIn implements IFeedbackContent.IProcessingIn {
    constructor(
        public branch : string
    ) { }
    public toString() {
        return `ProcessingIn(${this.branch})`
    }
}

export class WorkerStatus implements IFeedbackContent.IWorkerStatus {
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
