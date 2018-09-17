import * as Names from '../kernel/names'

export type T =
    ImplicitArg
// others...

export class ImplicitArg {
    constructor(
        public readonly c : Names.GlobalReference,
        public readonly nId : [number, Maybe<Names.Id.T>],
        public readonly forceInference : boolean,
    ) { }
}
