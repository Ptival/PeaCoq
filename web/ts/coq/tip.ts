// NOTE: On the OCaml side in Coq, these are used as polymorphic variants.

export class NewTip {
    private tag : 'NewTip'
}

export class Unfocus {
    private tag : 'Unfocus'
    constructor(
        public stateId : number
    ) { }
}

export class StmFocus {
    constructor(
        public start : number,
        public stop : number,
        public tip : number
    ) { }
}

export class Focus {
    constructor(
        public focus : StmFocus
    ) { }
}

export function parseNewTipOrUnfocus(s : string) : NewTip | Unfocus {
    switch(s) {
        case 'NewTip'  : return new NewTip()
        // TODO: case 'Unfocus' : return new Unfocus()
        default        : debugger; throw s
    }
}

export function fromString(s : string) : NewTip | Unfocus | StmFocus | Focus {
    switch(s) {
        case 'NewTip' : return new NewTip()
        default       : debugger; throw s
    }
}
