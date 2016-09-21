import { isBefore } from "./editor-utils"
import { Strictly } from "../peacoq/strictly"

export function setupUserInteractionForwardGoto(
  doc: ICoqDocument,
  forwardGoto$: Rx.Observable<AceAjax.Position>,
  errorMsg$: Rx.Observable<ErrorMessageFeedback>
): void {

  forwardGoto$
    .flatMap(dest => {
      return doc.sentences.sentenceCreated$
        // stop if the edit created ends after the destination position
        .takeWhile(e => isBefore(Strictly.Yes, e.stopPosition, dest))
        // stop if there's no text between the last edit and the destination
        .takeWhile(e => {
          const range = AceAjax.Range.fromPoints(e.stopPosition, dest)
          const text = doc.session.getDocument().getTextRange(range)
          return CoqStringUtils.coqTrimLeft(text) !== ""
        })
        // if an error occurs, abort
        .takeUntil(errorMsg$)
        // if another goto command occurs, abort and let the other one do the work
        .takeUntil(forwardGoto$)
        .map(_ => ({}))
        .startWith({})
    })
    .delay(0) // this is needed to set up the feedback loop properly
    .subscribe(() => doc.next())

}
