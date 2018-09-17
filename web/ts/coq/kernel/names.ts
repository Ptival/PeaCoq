import * as Pp from "../lib/pp"

export namespace Id {
    export type T = string
    export function print(id : T) : Pp.T { return Pp.str(id) }
    export function toString(id : T) : string { return id }
}

type Variable = Id.T

export namespace Name {

    export type T
        = Anonymous
        | Name

    export class Anonymous {}

    export class Name {
        constructor(
            public readonly id : string
        ) { }
    }

    export function print(n : T) : Pp.T {
        if (n instanceof Anonymous) { return Pp.str('_') }
        if (n instanceof Name) { return Id.print(n.id) }
        debugger
        throw n
    }

}

type ModuleIdent = Id.T

export namespace DirPath {

    export type T = ReadonlyArray<ModuleIdent>

    export function repr(x : T) : T { return x }

    export function toString(x : T) : string {
        if (x.length === 0) {
            return '<>'
        } else {
            return x.map(Id.toString).reverse().join('.')
        }
    }

}

export type GlobalReference
    = VarRef
    | ConstRef
    | IndRef
    | ConstructRef

export class VarRef {
    constructor(
        public readonly variable : Variable,
    ) { }
}

export class ConstRef {
    private tag : 'ConstRef'
    constructor(
        // public readonly constant : Constant.t,
    ) { }
}

export class IndRef {
    private tag : 'IndRef'
    constructor(
        // public readonly inductive : Inductive,
    ) { }
}

export class ConstructRef {
    private tag : 'ConstructRef'
    constructor(
        // public readonly ctor : Constructor,
    ) { }
}
