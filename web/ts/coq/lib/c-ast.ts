import { Maybe } from 'tsmonad'

import * as Loc from './loc'

export class cAST<A> {
    constructor(
        public readonly v : A,
        public readonly loc : Maybe<Loc.t>,
    ) { }
}

export function withVal<A, B>(f : (a : A) => B) : (c : cAST<A>) => B {
    return c => f(c.v)
}
