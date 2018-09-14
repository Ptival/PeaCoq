import { Cancel } from "../sertop/serapi-protocol"

// NOTE: CoqExn is pretty useless in indicating which command failed
// Feedback.ErrorMsg gives the failed state ID
// NOTE2: Except when the command fails wihtout a state ID! For instance
// if you 'Require Import Nonsense.' So need both?
export function setup(
    doc : ICoqDocument,
    error$ : Error$
) : void {
    error$.subscribe(e => {
        // We have to send a Cancel message so that the next Add acts on the
        // currently-valid state, rather than on the state that failed
        const cancel = new Cancel([e.spanId])
        doc.sendCommands(Rx.Observable.just(cancel))
        const failedStateId = e.spanId
        const failedSentence = doc.getSentenceByStateId(failedStateId)
        failedSentence.caseOf({
            nothing : () => {
                // This happens when commands fail before producing a state
            },
            just : s => doc.removeSentences(e => e.sentenceId >= s.sentenceId),
        })
    })
}
