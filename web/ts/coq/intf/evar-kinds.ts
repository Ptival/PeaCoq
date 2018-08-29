import * as Names from '../kernel/names'

export abstract class t {}
export class ImplicitArg extends t {
    constructor(
        public readonly c : Names.GlobalReference,
        public readonly nId : [number, Maybe<Names.Id.t>],
        public readonly forceInference : boolean,
    ) { super() }
}
