import { Maybe } from 'tsmonad'

import * as Loc from './loc'

export class cAST<A> {
    constructor(
        public readonly v : A,
        public readonly loc : Maybe<Loc.t>,
    ) { }
}
