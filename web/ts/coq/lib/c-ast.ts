import { Maybe } from 'tsmonad'

import * as Loc from './loc'

export class C_AST<A> {
    constructor(
        public readonly v : A,
        public readonly loc : Maybe<Loc.T>,
    ) { }
}

export function withVal<A, B>(f : (a : A) => B) : (c : C_AST<A>) => B {
    return c => f(c.v)
}
