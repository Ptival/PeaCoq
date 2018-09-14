import * as _ from 'lodash'

import * as Stage from './stage'
import * as PeaCoqUtils from '../peacoq/utils'

export function setup(
    doc : ICoqDocument,
    stmAdded$ : Added$
) : void {
    stmAdded$.subscribe(a => {
        // console.log('STM ADDED', a)
        const allSentences = doc.getSentencesToProcess()
        const sentence = _(allSentences).find(e => PeaCoqUtils.isJust(e.commandTag) && PeaCoqUtils.fromJust(e.commandTag) === a.cmdTag)
        if (!sentence) { return } // this happens for a number of reasons...
        const newStage = new Stage.BeingProcessed(sentence.stage, a.answer.stateId)
        sentence.setStage(newStage)
    })
}
