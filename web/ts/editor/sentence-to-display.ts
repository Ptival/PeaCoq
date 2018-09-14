import * as _ from 'lodash'

import { isBefore } from './editor-utils'
import * as DebugFlags from '../peacoq/debug-flags'
import { Strictly } from '../peacoq/strictly'

export function setup(doc : ICoqDocument) : Rx.Observable<ISentence<IStage>> {

    const editor = doc.editor

    const textCursorChangeEvent$ : Rx.Observable<{}> = Rx.Observable
        .create(observer => editor.selection.on('changeCursor', (e : any) => observer.onNext(e)))
        .share()

    const textCursorPosition$ = textCursorChangeEvent$
        .map(() => editor.selection.getCursor())
        .share()
    if (DebugFlags.textCursorPosition) { textCursorPosition$.subscribe(p => console.log(p)) }

    /*
      A sentence should be displayed if :
      - the cursor moves to a location where the sentence is under focus
      - a sentence got processed and no sentence is going to be processed
      The latter is necessary because the cursor doesn't move if the user processes
      a sentence while their cursor is already at the stop location.
    */

    const sentenceToBeDisplayedBecauseUnderCursor$ : Rx.Observable<ISentence<IStage>> =
        textCursorPosition$
        .debounce(250)
        .flatMap(pos => {
            // we want to display the last sentence whose stopPos is before `pos`
            const sentence = _(doc.getAllSentences())
                .findLast(s => isBefore(Strictly.No, s.stopPosition, pos))
            return sentence ? [sentence] : []
        })
        .distinctUntilChanged()
        .share()
    if (DebugFlags.sentenceToBeDisplayed) { sentenceToBeDisplayedBecauseUnderCursor$.subscribe(s => console.log(s)) }

    const sentenceToBeDisplayedBecauseLastBeingProcessed$ =
        doc.sentenceBeingProcessed$
        .filter(s => {
            const sentenceCount = doc.getSentencesToProcess().length + doc.getSentencesBeingProcessed().length
            return sentenceCount === 1 // this is the only sentence left, display it
        })
        .share()

    return Rx.Observable
        .merge([
            sentenceToBeDisplayedBecauseUnderCursor$,
            sentenceToBeDisplayedBecauseLastBeingProcessed$,
        ])
    // prevents the same sentence from triggering because under cursor and last processed
    // this might turn problematic if the user wants to redisplay it, maybe debounce would be better?
        .distinctUntilChanged()

}
