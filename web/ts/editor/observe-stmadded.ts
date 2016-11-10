import * as _ from "lodash"

import * as Stage from "./stage"

export function setup(
  doc: ICoqDocument,
  stmAdded$: StmAdded$
): void {
  stmAdded$.subscribe(a => {
    // console.log("STM ADDED", a)
    const allSentences = doc.getSentencesToProcess()
    const sentence = _(allSentences).find(e => isJust(e.commandTag) && fromJust(e.commandTag) === a.cmdTag)
    if (!sentence) { return } // this happens for a number of reasons...
    const newStage = new Stage.BeingProcessed(sentence.stage, a.answer.stateId)
    sentence.setStage(newStage)
  })
}
