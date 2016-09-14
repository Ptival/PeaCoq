import * as Stage from "./stage"

export function setup(
  doc: ICoqDocument,
  processed$: Rx.Observable<IFeedback<IFeedbackContent.IProcessed>>
): void {
  processed$
    .subscribe(f => {
      // console.log("PROCESSED", f)
      switch (f.editOrState) {
        case EditOrState.State:
          const stateId = f.editOrStateId
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
            // this can happen for two reasons:
            // - when reloading
            // - when some sentence fails, we sometimes get processed messages for later sentences
            // debugger
          }
          break
        default:
          debugger // not sure this ever happens
      }
    })
}
