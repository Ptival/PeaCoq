import * as _ from 'lodash'

import { setup as setupCancelBecauseBackwardGoTo } from './editor/cancel-because-backward-goto'
import { setup as setupCancelBecausePrev } from './editor/cancel-because-prev'
import { createGetCompletions } from './editor/completion'
import { CoqDocument } from './editor/coq-document'
import { setup as setupCoqtopPanel } from './editor/coqtop-panel'
import { ContextPanel } from './editor/context-panel'
import { setup as setupDisplayContext } from './editor/display-context'
import { setup as setupEditor } from './editor/editor'
import { update as fontSizeUpdate } from './editor/font-size'
import { setup as setupGoToPartitioning } from './editor/goto-partitioning'
import { setup as setupInFlightCounter } from './editor/in-flight-counter'
import { setup as setupKeybindings } from './editor/keybindings'
import { setup as setupLayout, rightLayoutName } from './editor/layout'
import { setup as setupNamesInScope } from './editor/names-in-scope'
import { setup as setupObserveContext } from './editor/observe-context'
import { setup as setupObserveCoqExn } from './editor/observe-coqexn'
import { setup as setupObserveEditorChange } from './editor/observe-editor-change'
import { setup as setupObserveError } from './editor/observe-error'
import { setup as setupObserveProcessed } from './editor/observe-processed'
import { setup as setupObserveStmAdded } from './editor/observe-stmadded'
import { setup as setupObserveStmCancel } from './editor/observe-stmcancel'
import { setupProgressBar } from './editor/progress-bar'
import { setup as setupQuitBecauseFileLoaded } from './editor/quit-because-file-loaded'
import { setup as setupSyntaxHovering } from './editor/syntax-hovering'
import { setupTextCursorPositionUpdate } from './editor/text-cursor-position'
import { setup as setupToolbar } from './editor/toolbar'
import { setup as setupUnderlineError } from './editor/underline-errors'
import { setup as setupUserActions } from './editor/user-actions'
import { setupUserInteractionForwardGoto } from './editor/user-interaction-forward-goto'

import * as Filters from './peacoq/filters'
import { onResize } from './peacoq/on-resize'
import * as Theme from './peacoq/theme'

import { setup as setupProofTreeAutomation } from './prooftree/automation'
import { setup as setupProofTreePopulating } from './prooftree/populating'
import { setup as setupProofTree } from './prooftree/setup'

// import * as Promise from 'bluebird'
// Promise.longStackTraces()
// Promise.onUnhandledRejectionHandled((reason, promise) => {
//   debugger
// })

let lastTimer = Date.now()
function time(label : string) {
    const now = Date.now()
    const delta = now - lastTimer
    if (delta > 5) {
        console.log(`Timing ${label} : ${now - lastTimer}ms`)
    }
    lastTimer = now
}

const resizeBufferingTime = 250 // milliseconds

$(document).ready(() => {

    const readyStartTime = Date.now()

    const {
        bottomLayout,
        contextTabs,
        layoutResizeStream,
        rightLayout,
        rightLayoutRenderedStream,
        rightLayoutResizeStream,
        windowResizeStream,
    } = setupLayout()

    const resize$ =
        Rx.Observable.merge(windowResizeStream, layoutResizeStream, rightLayoutResizeStream)
    // only fire once every <resizeBufferingTime> milliseconds
        .bufferWithTime(resizeBufferingTime).filter(a => !_.isEmpty(a))

    const editor = ace.edit('editor')

    const doc : ICoqDocument = new CoqDocument(editor)

    bottomLayout.on({ type : 'render', execute : 'after' }, () => {
        setupProgressBar(doc)
        bottomLayout.refresh()
    })

    const tabsAreReadyPromise = new Promise(onFulfilled => {
        rightLayoutRenderedStream.take(1).subscribe(() => {
            // top panes
            contextTabs.click('pretty')
            doc.contextPanel = new ContextPanel(doc, rightLayoutName)
            // TODO : stream this
            fontSizeUpdate(doc)
            onFulfilled()
        })
    })

    time('start')
    setupDisplayContext(doc)
    time('A0')
    setupObserveEditorChange(doc)
    time('B0')
    setupEditor(doc, editor)
    time('C0')
    editor.focus()
    time('D0')
    resize$.subscribe(() => onResize(doc))
    time('E0')

    time('A1')

    // SLOW!
    // const toolbar$s = setupToolbar(doc)
    const toolbar$s = {
        fontDecrease : Rx.Observable.empty(),
        fontIncrease : Rx.Observable.empty(),
        goToCaret : Rx.Observable.empty(),
        load : Rx.Observable.empty(),
        next : Rx.Observable.empty(),
        previous : Rx.Observable.empty(),
        save : Rx.Observable.empty(),
    }

    time('B1')
    const shortcut$s = setupKeybindings(doc)
    time('C1')
    const { goTo$, loadedFile$, next$, prev$ } = setupUserActions(doc, toolbar$s, shortcut$s)
    time('D1')

    time('A2')
    const [forwardGoTo$, backwardGoTo$] = setupGoToPartitioning(doc, goTo$)
    time('B2')
    setupCancelBecauseBackwardGoTo(doc, backwardGoTo$)
    time('C2')
    loadedFile$.subscribe(() => doc.contextPanel.clear())
    time('D2')
    setupQuitBecauseFileLoaded(doc, loadedFile$)
    time('E2')
    next$.subscribe(() => doc.next())
    time('F2')
    setupCancelBecausePrev(doc, prev$)
    time('G2')

    time('A3')
    setupSyntaxHovering()
    time('B3')
    tabsAreReadyPromise.then(() => Theme.setupTheme(doc))
    time('C3')
    Theme.afterChange$.subscribe(() => onResize(doc))
    time('D3')
    // These also help with the initial display...
    Theme.afterChange$.subscribe(() => { rightLayout.refresh() })
    time('E3')
    Theme.afterChange$.subscribe(() => { bottomLayout.refresh() })
    time('F3')

    // Automated tasks need to stop whenever the user changes the current state
    const stopAutomationRound$ : Rx.Observable<{}> = Rx.Observable.empty() // FIXME URGENT

    time('F4')

    // This is pretty slow
    // doc.editor.completers = [{ getCompletions : createGetCompletions(doc, stopAutomationRound$) }]

    time('F5')

    // Shorthands for input streams
    time('F6')
    const controlCommand$ = doc.input$.let(Filters.controlCommand)
    time('F7')
    const stmAdd$ = controlCommand$.let(Filters.stmAdd)
    time('F8')
    const stmCancel$ = controlCommand$.let(Filters.stmCancel)
    time('F9')
    const stmEditAt$ = controlCommand$.let(Filters.stmEditAt)
    time('F10')
    const stmQuery$ = controlCommand$.let(Filters.stmQuery)
    time('F11')

    // Shorthands for output streams
    const { answer$s, feedback$s } = doc.output$s
    time('F12')
    const { completed$, coqExn$, stmAdded$, stmCanceled$ } = answer$s
    time('F13')
    const { error$, notice$ } = feedback$s.message$s
    time('F14')
    const { processed$ } = feedback$s
    time('F15')

    time('A4')
    setupObserveContext(doc, notice$, stmQuery$)
    time('B4')
    const stmActionsInFlightCounter$ = setupInFlightCounter(stmAdd$, stmCancel$, stmEditAt$, completed$)
    time('C4')
    // setupProofTreeAutomation(completed$, doc, error$, notice$, stmActionsInFlightCounter$, stmAdded$, stopAutomationRound$)
    setupProofTreePopulating(doc, doc.tip$)
    time('D4')
    setupObserveStmAdded(doc, stmAdded$)
    time('E4')
    setupUserInteractionForwardGoto(doc, forwardGoTo$, error$)
    time('F4')
    setupObserveProcessed(doc, processed$)
    time('G4')

    time('A5')
    setupUnderlineError(doc, error$) // keep this above the subscription that removes edits
    time('b5')
    const jBottom = $(w2ui[rightLayoutName].get('bottom').content)
    time('c5')
    setupCoqtopPanel(doc, jBottom, error$, notice$, loadedFile$) // keep this above the subscription that removes edits
    time('D5')

    /***** IMPORTANT :
     * The following lines remove edits from the document, so their subscription
     * must happen after subscriptions that want to inspect the edits before removal.
     * TODO : design it better so that removed edits are streamed out.
     *****/
    time('A6')
    setupObserveCoqExn(doc, coqExn$, stmAdd$, stmQuery$, completed$)
    time('B6')
    setupObserveError(doc, error$)
    time('C6')

    time('A7')
    // debugging
    coqExn$
        .filter(e => e.answer.getMessage().indexOf('Anomaly') >= 0)
        .subscribe(e => { debugger })
    time('B7')

    time('A8')
    const stmCanceledFiltered$ = setupObserveStmCancel(doc, stmCancel$, stmCanceled$)
    time('B8')
    setupProofTree(doc, loadedFile$, resize$, stmCanceledFiltered$, bottomLayout)
    time('C8')
    const namesInScope$ = setupNamesInScope(doc, completed$, notice$, stmAdded$)
    time('D8')
    namesInScope$.subscribe(names => console.log(`${names.length} names in scope`))
    time('E8')

    time('A9')
    // Debugging :
    doc.editor.setValue(`
Theorem test : forall x, (and (or (x = 0) (x > 0)) (x >= 0)).
Proof.
  intros.

Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day
.
`)
    time('B9')

    const readyStopTime = Date.now()
    console.log(`Ready handler executed in ${readyStopTime - readyStartTime}ms`)

})
