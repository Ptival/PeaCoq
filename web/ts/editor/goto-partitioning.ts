import * as _ from 'lodash'

import { isBefore } from './editor-utils'
import { Strictly } from '../peacoq/strictly'

interface GoToPositions {
    destinationPos : AceAjax.Position
    lastEditStopPos : AceAjax.Position
}

export function setup(
    doc : ICoqDocument,
    goTo$ : Rx.Observable<{}>
) : [Rx.Observable<AceAjax.Position>, Rx.Observable<AceAjax.Position>] {
    const [forward, backward] = goTo$
    // filter out when position is already reached
        .flatMap<GoToPositions>(() => {
            const lastEditStopPos = doc.getLastSentenceStop()
            const destinationPos = doc.editor.getCursorPosition()
            return (
                _.isEqual(lastEditStopPos, destinationPos)
                    ? []
                    : [{ destinationPos : destinationPos, lastEditStopPos : lastEditStopPos, }]
            )
        })
    // partition on the direction of the goTo
        .partition(o => isBefore(Strictly.Yes, o.lastEditStopPos, o.destinationPos))
    return [forward.map(p => p.destinationPos), backward.map(p => p.destinationPos)]
}
