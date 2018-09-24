import * as _ from 'lodash'
import { Maybe } from 'tsmonad'

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
import { ProofTree } from './prooftree/prooftree'
import { setup as setupProofTree } from './prooftree/setup'

import * as C_AST from './coq/lib/c-ast'
import * as ConstrExpr from './coq/intf/constr-expr'
import { PeaCoqGoal } from './peacoq/goal';

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

function displayProofTree() {

    const {
        bottomLayout,
        contextTabs,
        layoutResizeStream,
        rightLayout,
        rightLayoutRenderedStream,
        rightLayoutResizeStream,
        windowResizeStream,
    } = setupLayout()

    const editor = ace.edit('editor')

    const doc : ICoqDocument = new CoqDocument(editor)

    const goal : PeaCoqContextElement = {
        goal : {
            goalId : 0,
            goalHyp : ["HELLO", "I", "AM", "ERROR"],
            goalCcl : "SUP?",
        },
        ppgoal : new PeaCoqGoal(
            [],
            new C_AST.C_AST(
                new ConstrExpr.CPrim(new PrimTokenString('I AM CONCL')),
                Maybe.nothing()
            )
        ),
    }

    const context : PeaCoqContext = {
        fgGoals : [goal],
        bgGoals : [],
        shelvedGoals : [],
        givenUpGoals : [],
    }

    const anchor = document.getElementById('interface')
    if (!anchor) {
        debugger
        throw anchor
    }

    const pt = new ProofTree(
        'DEBUG',
        anchor,
        anchor.clientWidth,
        anchor.clientHeight,
        context,
        0,
        doc
    )

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

    tabsAreReadyPromise.then(() => Theme.setupTheme(doc))

}

$(document).ready(() => {

    // displayProofTree()
    // return

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

    setupDisplayContext(doc)
    setupObserveEditorChange(doc)
    setupEditor(doc, editor)
    editor.focus()
    resize$.subscribe(() => onResize(doc))

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

    const shortcut$s = setupKeybindings(doc)
    const { goTo$, loadedFile$, next$, prev$ } = setupUserActions(doc, toolbar$s, shortcut$s)

    const [forwardGoTo$, backwardGoTo$] = setupGoToPartitioning(doc, goTo$)
    setupCancelBecauseBackwardGoTo(doc, backwardGoTo$)
    loadedFile$.subscribe(() => doc.contextPanel.clear())
    setupQuitBecauseFileLoaded(doc, loadedFile$)
    next$.subscribe(() => doc.next())
    setupCancelBecausePrev(doc, prev$)

    setupSyntaxHovering()
    tabsAreReadyPromise.then(() => Theme.setupTheme(doc))
    Theme.afterChange$.subscribe(() => onResize(doc))
    // These also help with the initial display...
    Theme.afterChange$.subscribe(() => { rightLayout.refresh() })
    Theme.afterChange$.subscribe(() => { bottomLayout.refresh() })

    // Automated tasks need to stop whenever the user changes the current state
    const stopAutomationRound$ : Rx.Observable<{}> = Rx.Observable.empty() // FIXME URGENT

    // This is pretty slow
    // doc.editor.completers = [{ getCompletions : createGetCompletions(doc, stopAutomationRound$) }]

    // Shorthands for input streams
    const cmd$ = doc.input$
    const stmAdd$    = cmd$.let(Filters.Cmd.add)
    const stmCancel$ = cmd$.let(Filters.Cmd.cancel)
    const stmQuery$  = cmd$.let(Filters.Cmd.query)

    // Shorthands for output streams
    const { answer$s, feedback$s } = doc.output$s
    const { completed$, coqExn$, stmAdded$, stmCanceled$ } = answer$s
    const { error$, notice$ } = feedback$s.message$s
    const { processed$ } = feedback$s

    setupObserveContext(doc, notice$, stmQuery$)
    const stmActionsInFlightCounter$ = setupInFlightCounter(stmAdd$, stmCancel$, completed$)
    // setupProofTreeAutomation(completed$, doc, error$, notice$, stmActionsInFlightCounter$, stmAdded$, stopAutomationRound$)
    setupProofTreePopulating(doc, doc.tip$)
    setupObserveStmAdded(doc, stmAdded$)
    setupUserInteractionForwardGoto(doc, forwardGoTo$, error$)
    setupObserveProcessed(doc, processed$)

    setupUnderlineError(doc, error$) // keep this above the subscription that removes edits
    const jBottom = $(w2ui[rightLayoutName].get('bottom').content)
    setupCoqtopPanel(doc, jBottom, error$, notice$, loadedFile$) // keep this above the subscription that removes edits

    /***** IMPORTANT :
     * The following lines remove edits from the document, so their subscription
     * must happen after subscriptions that want to inspect the edits before removal.
     * TODO : design it better so that removed edits are streamed out.
     *****/
    setupObserveCoqExn(doc, coqExn$, stmAdd$, stmQuery$, completed$)
    setupObserveError(doc, error$)

    // debugging
    coqExn$
        .filter(e => e.answer.getMessage().indexOf('Anomaly') >= 0)
        .subscribe(e => { debugger })

    const stmCanceledFiltered$ = setupObserveStmCancel(doc, stmCancel$, stmCanceled$)
    setupProofTree(doc, loadedFile$, resize$, stmCanceledFiltered$, bottomLayout)
    const namesInScope$ = setupNamesInScope(doc, completed$, notice$, stmAdded$)
    namesInScope$.subscribe(names => console.log(`${names.length} names in scope`))

    // Debugging :
    doc.editor.setValue(`
Theorem swap : forall (A B : Prop), A /\\ B -> B /\\ A.
Proof.
  intros A B H.
  destruct H as [HA HB].
  split.

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

    const readyStopTime = Date.now()
    console.log(`Ready handler executed in ${readyStopTime - readyStartTime}ms`)

})
