export type ParenRelation
    = E
    | L
    | Prec
    | Any

export class E {
    private tag : 'E'
}

export class L {
    private tag : 'L'
}

export class Prec {
    constructor(public precedence : number) { }
}

export class Any {
    private tag : 'Any'
}
