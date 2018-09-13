import { escapeQuotes } from './utils'

export type QueryCommand
    = Goals
    | Vernac

export class Goals {
    constructor() { }
    public toSexp() : string {
        return `Goals`
    }
}

export class Vernac {
    constructor(
        public readonly vernac : string
    ) { }
    public toSexp() : string {
        return `(Vernac "${escapeQuotes(this.vernac)}")`
    }
}
