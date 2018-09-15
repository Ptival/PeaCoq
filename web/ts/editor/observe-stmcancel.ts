import * as _ from 'lodash'
import { Maybe } from 'tsmonad'
import { Answer } from '../sertop/answer'
import { Canceled } from '../sertop/answer-kind'

export function setup(
    doc : ICoqDocument,
    stmCancel$ : Cancel$,
    stmCanceled$ : Canceled$
) : Canceled$ {
    const stmCanceledFiltered$ = new Rx.Subject<Answer.Answer<Canceled>>()

    // Now that we pre-emptively removed sentences from the view before they are
    // acknowledged by the backend, checking which StmCanceled were caused by
    // PeaCoq's automation is more complex than checking if the removed stateIds
    // match a sentence in the document.
    stmCancel$
    // .filter(c => !c.controlCommand.fromAutomation)
        .flatMap(c => stmCanceled$.filter(e => e.cmdTag === c.cmdTag))
        .subscribe(a => {
            const removedStateIds = a.answer.stateIds
            stmCanceledFiltered$.onNext(a)
            doc.removeSentencesByStateIds(removedStateIds)
            const tip = _.maxBy(doc.getAllSentences(), s => s.sentenceId)
            doc.setTip(tip ? Maybe.just(tip) : Maybe.nothing<ISentence<IStage>>())
        })

    return stmCanceledFiltered$
}
