import { escapeQuotes } from './utils'

export class Goals implements ISertop.IQueryCommand.IGoals {
    constructor() { }
    public toSexp() : string {
        return `Goals`
    }
}

export class Vernac implements ISertop.IQueryCommand.IVernac {
    constructor(
        public readonly vernac : string
    ) { }
    public toSexp() : string {
        return `(Vernac "${escapeQuotes(this.vernac)}")`
    }
}
