import * as _ from 'lodash'

import { Cancel } from '../sertop/serapi-protocol'

export function setup(
    doc : ICoqDocument,
    prev$ : Rx.Observable<{}>
) : void {

    const sentenceToCancelBecausePrev$ : Rx.Observable<ISentence<IStage>> =
        prev$
        .flatMap(({}) => {
            if (doc.getSentencesToProcess().length > 0) { return [] }
            const max = _.maxBy(doc.getAllSentences(), s => s.sentenceId)
            if (!max) { return [] }
            return [max]
        })
        .share()

    sentenceToCancelBecausePrev$.subscribe(s => {
        doc.moveCursorToPositionAndCenter(s.startPosition)
    })

    sentenceToCancelBecausePrev$
        .flatMap(s =>
                 s.getStateId().caseOf({
                     nothing: () => [],
                     just: sid => [sid],
                 })
                )
        .map(sid => Rx.Observable.just(new Cancel([sid])))
        .subscribe(cmd$ => doc.sendCommands(cmd$))

}
