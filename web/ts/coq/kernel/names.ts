import * as Pp from "../lib/pp"

export namespace Id {
    export type t = string
    export function print(id : t) : Pp.t { return Pp.str(id) }
    export function toString(id : t) : string { return id }
}

type Variable = Id.t

export namespace Name {
    export abstract class t {}

    export class Anonymous extends t {}

    export class Name extends t {
        constructor(
            public readonly id : string
        ) { super() }
    }

    export function print(n : t) : Pp.t {
        if (n instanceof Anonymous) { return Pp.str('_') }
        if (n instanceof Name) { return Id.print(n.id) }
        throw n
    }

}

type ModuleIdent = Id.t

export namespace DirPath {
    export type t = ReadonlyArray<ModuleIdent>
    export function repr(x : t) : t { return x }

    export function toString(x : t) : string {
        if (x.length === 0) {
            return '<>'
        } else {
            return x.map(Id.toString).reverse().join('.')
        }
    }
}

export abstract class GlobalReference {}

export class VarRef extends GlobalReference {
    constructor(
        public readonly variable : Variable,
    ) { super() }
}

export class ConstRef extends GlobalReference {
    constructor(
        // public readonly constant : Constant.t,
    ) { super() }
}

export class IndRef extends GlobalReference {
    constructor(
        // public readonly inductive : Inductive,
    ) { super() }
}

export class ConstructRef extends GlobalReference {
    constructor(
        // public readonly ctor : Constructor,
    ) { super() }
}
