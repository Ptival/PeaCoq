import * as _ from 'lodash'

import * as Stage from './stage'

export function setup(
    doc : ICoqDocument,
    processed$ : Processed$
) : void {
    processed$
        .subscribe(f => {
            // console.log('PROCESSED', f)
            const stateId = f.spanId
            const editsBeingProcessed = doc.getSentencesBeingProcessed()
            const sentence = _(editsBeingProcessed).find(e => e.stage.stateId === stateId)
            if (sentence) {
                const newStage = new Stage.Processed(doc, sentence.stage)
                sentence.setStage(newStage)
                // if (
                //   Global.coqDocument.getSentencesToProcess().length === 0
                //   && Global.coqDocument.getSentencesBeingProcessed().length === 0
                // ) {
                //   Global.coqDocument.moveCursorToPositionAndCenter(sentence.stopPosition)
                // }
            } else {
                // this can happen for two reasons :
                // - when reloading
                // - when some sentence fails, we sometimes get processed messages for later sentences
                // debugger
            }
        })
}
