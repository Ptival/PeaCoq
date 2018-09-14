import { Maybe } from 'tsmonad'

import * as PeaCoqUtils from '../peacoq/utils'

export class ValueFail implements IValueFail {
    public stateId : number
    public location : Maybe<ErrorLocation>
    public message : string
    constructor(v : [number, [number, number] | undefined, string]) {
        this.stateId = v[0]
        this.location = Maybe.nothing<ErrorLocation>()
        const loc = v[1]
        if (loc !== undefined) {
            const [startPos, stopPos] = loc
            this.location = Maybe.just({ startPos : startPos, stopPos : stopPos })
        }
        this.message = PeaCoqUtils.trimSpacesAround(PeaCoqUtils.unbsp(v[2]))
    }
}
