import { setup as setupCancelBecauseBackwardGoTo } from "./editor/cancel-because-backward-goto";
import { setup as setupCancelBecausePrev } from "./editor/cancel-because-prev";
import { createGetCompletions } from "./editor/completion";
import { CoqDocument } from "./editor/coq-document";
import { setup as setupCoqtopPanel } from "./editor/coqtop-panel";
import { ContextPanel } from "./editor/context-panel";
import { setup as setupDisplayContext } from "./editor/display-context";
import { setup as setupEditor } from "./editor/editor";
import { update as fontSizeUpdate } from "./editor/font-size";
import { setup as setupGoToPartitioning } from "./editor/goto-partitioning";
import { setup as setupInFlightCounter } from "./editor/in-flight-counter";
import { setup as setupKeybindings } from "./editor/keybindings";
import { setup as setupLayout, rightLayoutName } from "./editor/layout";
import { setup as setupNamesInScope } from "./editor/names-in-scope";
import { setup as setupObserveContext } from "./editor/observe-context";
import { setup as setupObserveCoqExn } from "./editor/observe-coqexn";
import { setup as setupObserveEditorChange } from "./editor/observe-editor-change";
import { setup as setupObserveError } from "./editor/observe-error";
import { setup as setupObserveProcessed } from "./editor/observe-processed";
import { setup as setupObserveStmAdded } from "./editor/observe-stmadded";
import { setup as setupObserveStmCancel } from "./editor/observe-stmcancel";
import { setupProgressBar } from "./editor/progress-bar";
import { setup as setupQuitBecauseFileLoaded } from "./editor/quit-because-file-loaded";
import { setup as setupSyntaxHovering } from "./editor/syntax-hovering";
import { setupTextCursorPositionUpdate } from "./editor/text-cursor-position";
import { setup as setupToolbar } from "./editor/toolbar";
import { setup as setupUnderlineError } from "./editor/underline-errors";
import { setup as setupUserActions } from "./editor/user-actions";
import { setupUserInteractionForwardGoto } from "./editor/user-interaction-forward-goto";

import * as Filters from "./peacoq/filters";
import { onResize } from "./peacoq/on-resize";
import * as Theme from "./peacoq/theme";

import { setup as setupProofTreeAutomation } from "./prooftree/automation";
import { setup as setupProofTreePopulating } from "./prooftree/populating";
import { setup as setupProofTree } from "./prooftree/setup";



// import * as Promise from 'bluebird';
// Promise.longStackTraces();
// Promise.onUnhandledRejectionHandled((reason, promise) => {
//   debugger;
// });

const resizeBufferingTime = 250; // milliseconds

$(document).ready(() => {

  const {
    bottomLayout,
    contextTabs,
    layoutResizeStream,
    rightLayout,
    rightLayoutRenderedStream,
    rightLayoutResizeStream,
    windowResizeStream,
  } = setupLayout();

  const resize$ =
    Rx.Observable.merge(windowResizeStream, layoutResizeStream, rightLayoutResizeStream)
      // only fire once every <resizeBufferingTime> milliseconds
      .bufferWithTime(resizeBufferingTime).filter(a => !_.isEmpty(a));

  const editor = ace.edit("editor");

  const doc: ICoqDocument = new CoqDocument(editor);

  bottomLayout.on({ type: "render", execute: "after" }, () => {
    setupProgressBar(doc);
    bottomLayout.refresh();
  });

  const tabsAreReadyPromise = new Promise(onFulfilled => {
    rightLayoutRenderedStream.take(1).subscribe(() => {
      const tabs: ITabs = <any>{};
      // top panes
      contextTabs.click("pretty");
      doc.contextPanel = new ContextPanel(doc, rightLayoutName);
      // TODO: stream this
      fontSizeUpdate(doc);
      onFulfilled();
    });
  });

  setupDisplayContext(doc);
  setupObserveEditorChange(doc);
  setupEditor(doc, editor);
  editor.focus();
  resize$.subscribe(() => onResize(doc));

  const toolbar$s = setupToolbar(doc);
  const shortcut$s = setupKeybindings(doc);
  const { goTo$, loadedFile$, next$, prev$ } = setupUserActions(doc, toolbar$s, shortcut$s);

  const [forwardGoTo$, backwardGoTo$] = setupGoToPartitioning(doc, goTo$);
  setupCancelBecauseBackwardGoTo(doc, backwardGoTo$);
  loadedFile$.subscribe(() => doc.contextPanel.clear());
  setupQuitBecauseFileLoaded(doc, loadedFile$);
  next$.subscribe(() => doc.next());
  setupCancelBecausePrev(doc, prev$);

  setupSyntaxHovering();
  tabsAreReadyPromise.then(() => Theme.setupTheme(doc));
  Theme.afterChange$.subscribe(() => onResize(doc));
  // These also help with the initial display...
  Theme.afterChange$.subscribe(() => { rightLayout.refresh(); });
  Theme.afterChange$.subscribe(() => { bottomLayout.refresh(); });

  // Automated tasks need to stop whenever the user changes the current state
  const stopAutomationRound$: Rx.Observable<{}> = Rx.Observable.empty(); // FIXME URGENT

  doc.editor.completers = [{ getCompletions: createGetCompletions(doc, stopAutomationRound$) }];

  // Shorthands for input streams
  const controlCommand$ = doc.input$.let(Filters.controlCommand);
  const stmAdd$ = controlCommand$.let(Filters.stmAdd);
  const stmCancel$ = controlCommand$.let(Filters.stmCancel);
  const stmEditAt$ = controlCommand$.let(Filters.stmEditAt);
  const stmQuery$ = controlCommand$.let(Filters.stmQuery);

  // Shorthands for output streams
  const { answer$s, feedback$s } = doc.output$s;
  const { completed$, coqExn$, stmAdded$, stmCanceled$ } = answer$s;
  const { error$, notice$ } = feedback$s.message$s;
  const { processed$ } = feedback$s;

  setupObserveContext(doc, notice$, stmQuery$);
  const stmActionsInFlightCounter$ = setupInFlightCounter(stmAdd$, stmCancel$, stmEditAt$, completed$);
  // setupProofTreeAutomation(completed$, doc, error$, notice$, stmActionsInFlightCounter$, stmAdded$, stopAutomationRound$);
  setupProofTreePopulating(doc, doc.tip$);
  setupObserveStmAdded(doc, stmAdded$);
  setupUserInteractionForwardGoto(doc, forwardGoTo$, error$);
  setupObserveProcessed(doc, processed$);

  setupUnderlineError(doc, error$); // keep this above the subscription that removes edits
  const jBottom = $(w2ui[rightLayoutName].get("bottom").content);
  setupCoqtopPanel(doc, jBottom, error$, notice$, loadedFile$); // keep this above the subscription that removes edits

  /***** IMPORTANT:
   * The following lines remove edits from the document, so their subscription
   * must happen after subscriptions that want to inspect the edits before removal.
   * TODO: design it better so that removed edits are streamed out.
   *****/
  setupObserveCoqExn(doc, coqExn$, stmAdd$, stmQuery$, completed$);
  setupObserveError(doc, error$);

  // debugging
  coqExn$
    .filter(e => e.answer.getMessage().indexOf("Anomaly") >= 0)
    .subscribe(e => { debugger; });

  const stmCanceledFiltered$ = setupObserveStmCancel(doc, stmCancel$, stmCanceled$);
  setupProofTree(doc, loadedFile$, resize$, stmCanceledFiltered$, bottomLayout);

  const namesInScope$ = setupNamesInScope(doc, notice$);

  namesInScope$.subscribe(names => console.log(`${names.length} names in scope`));

  // Debugging:
  doc.editor.setValue(`
    Inductive day : Type :=
    | monday : day
    | tuesday : day
    | wednesday : day
    | thursday : day
    | friday : day
    | saturday : day
    | sunday : day
    .
  `);

});
