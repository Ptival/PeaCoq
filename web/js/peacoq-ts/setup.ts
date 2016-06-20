import * as FeedbackContent from "./coq/feedback-content";

import * as Coq85 from "./editor/coq85";
import { CoqDocument } from "./editor/coq-document";
import { CoqtopPanel } from "./editor/coqtop-panel";
import { ContextPanel } from "./editor/context-panel";
import * as Edit from "./editor/edit";
import { setupEditor } from "./editor/editor";

import { isBefore } from "./editor/editor-utils";
import { pimpMyError } from "./editor/error";
import { setupKeybindings } from "./editor/keybindings";
import { setupProgressBar } from "./editor/progress-bar";

import { setupTextCursorPositionUpdate } from "./editor/text-cursor-position";
import { setupUserInteractionForwardGoto } from "./editor/user-interaction-forward-goto";
// // TODO: toolbar.ts should setup{Load,Save}File upon setupToolbar
// // TODO: unless it can't because of keybindings?
import { pickFile, saveFile, setupLoadFile, setupToolbar, setupSaveFile } from "./editor/toolbar";

import { emptyContext } from "./peacoq/peacoq";

// TODO: not sure if this file should be creating those nodes...
import { GoalNode } from "./prooftree/goalnode";
import { ProofTree } from "./prooftree/prooftree";
import { Tactic } from "./prooftree/tactic";
import { TacticGroupNode } from "./prooftree/tacticgroupnode";
import { getActiveProofTree } from "./prooftree/utils";
import { proofTreeOnEdit, proofTreeOnEditAt } from "./prooftree/prooftree-handlers";

import * as Coqtop from "./coqtop-rx";
import * as CoqtopInput from "./coqtop-input";
import * as DebugFlags from "./debug-flags";
import * as Global from "./global-variables";
import { PeaCoqGoal } from "./peacoq-goal";
import { Strictly } from "./strictly";
import * as Theme from "./theme";

let fontSize = 16; // pixels
const resizeBufferingTime = 250; // milliseconds

// TODO: this should not be global
let layout: W2UI.W2Layout;
let bottomLayout: W2UI.W2Layout;
// const rightLayout: W2UI.W2Layout;
// const contextTabs: W2UI.W2Tabs;
// const coqtopTabs: W2UI.W2Tabs;

$(document).ready(() => {

  $("#interface").w2layout({
    name: "layout",
    panels: [
      { type: "top", size: 34, resizable: false, content: $("<div>", { id: "toolbar" }) },
      { type: "left", size: "50%", overflow: "hidden", resizable: true, content: $("<div>", { id: "editor", style: "height: 100%" }) },
      { type: "main", size: "50%", overflow: "hidden", content: $("<div>", { id: "right" }) },
      { type: "bottom", size: "20px", overflow: "hidden", resizable: false, content: $("<div>", { id: "bottom" }) },
    ]
  });

  const editor = ace.edit("editor");
  const textCursorChangeEvent$ = Rx.Observable
    .create(observer => {
      editor.selection.on("changeCursor", e => { observer.onNext(e); });
    })
    .share();

  const textCursorPosition$ = textCursorChangeEvent$
    .map(() => editor.selection.getCursor());
  if (DebugFlags.textCursorPosition) { subscribeAndLog(textCursorPosition$); }

  /* nothing() if no edit to display, just(edit) if there is one */
  const editToBeDisplayed$: Rx.Observable<Maybe<ISentence<IEditStage>>> =
    textCursorPosition$
      .map(pos => {
        // we want to display the last edit whose stopPos is before `pos`
        const edit = _(Global.coqDocument.getAllEdits())
          .findLast(s => isBefore(Strictly.No, s.stopPosition, pos));
        return edit ? just(edit) : nothing();
      })
      .distinctUntilChanged();
  if (DebugFlags.editToBeDisplayed) { subscribeAndLog(editToBeDisplayed$); }

  editToBeDisplayed$
    .flatMapLatest(edit => edit.caseOf({
      nothing: () => Promise.resolve(emptyContext),
      just: e => e.getProcessedStage().then(s => s.getContext()),
    }))
    .subscribe(context => Global.coqDocument.contextPanel.display(context));

  Global.setCoqDocument(new CoqDocument(editor));

  const editAtBecauseEditorChange: Rx.Observable<ICoqtopInput> =
    Global.coqDocument.editorChange$
      .flatMap(change => {
        const maybeEdit = Global.coqDocument.getEditAtPosition(minPos(change.start, change.end));
        // debugger;
        return (
          maybeEdit
            .bind(e => e.getPreviousStateId())
            .fmap(s => new CoqtopInput.EditAt(s))
            .caseOf({
              nothing: () => [],
              just: i => [i],
            })
        );
      })
      .share();

  setupEditor(editor);
  editor.focus();

  const rightLayoutName = "right-layout";
  const bottomLayoutName = "bottom-layout";

  $().w2layout({
    name: rightLayoutName,
    panels: [
      { type: "main", size: "50%", resizable: true, tabs: { tabs: [], } },
      { type: "bottom", size: "50%", resizable: true, content: $("<div>", { id: "bottom-right" }) },
    ],
  });

  $().w2layout({
    name: bottomLayoutName,
    panels: [
      { type: "top", size: "90%", hidden: true, resizable: false, content: $("<div>", { id: "prooftree" }) },
      { type: "main", size: "10%", overflow: "hidden", resizable: false, content: $("<div>", { id: "progress-bar", height: "100%" }) },
    ],
  });

  layout = w2ui["layout"];
  const rightLayout = w2ui[rightLayoutName];
  bottomLayout = w2ui[bottomLayoutName];
  const contextTabs = w2ui[rightLayoutName + "_main_tabs"];
  contextTabs.onClick = function(event: W2UI.W2Event) { $("#myTabsContent").html(event.target); };
  const coqtopTabs = w2ui[rightLayoutName + "_bottom_tabs"];

  bottomLayout.on({ type: "render", execute: "after" }, () => {
    setupProgressBar();
    bottomLayout.refresh();
  });

  const rightLayoutRenderedStream = Rx.Observable
    .create(observer => {
      rightLayout.on({ type: "render", execute: "after" }, () => observer.onNext({}));
    })
    .share();

  const tabsAreReadyPromise = new Promise(onFulfilled => {
    rightLayoutRenderedStream.take(1).subscribe(() => {

      const tabs: ITabs = <any>{};

      // top panes

      contextTabs.click("pretty");

      Global.coqDocument.contextPanel = new ContextPanel(Global.coqDocument, rightLayoutName);

      // TODO: stream this
      updateFontSize(Global.coqDocument);

      onFulfilled();
    });

  });

  layout.content("main", rightLayout);
  layout.content("bottom", bottomLayout);

  const windowResizeStream: Rx.Observable<{}> = Rx.Observable.fromEvent($(window), "resize");
  const layoutResizeStream = setupW2LayoutResizeStream(layout);
  const rightLayoutResizeStream = setupW2LayoutResizeStream(rightLayout);

  const resize$ =
    Rx.Observable.merge(windowResizeStream, layoutResizeStream, rightLayoutResizeStream)
    // only fire once every <resizeBufferingTime> milliseconds
    .bufferWithTime(resizeBufferingTime).filter(a => !_.isEmpty(a));

  resize$.subscribe(onResize);
  resize$.subscribe(() => Global.coqDocument.contextPanel.onResize());

  // TODO: this is probably needed so that the main editor stays centered
  // when the prooftree panel showsup or hides
  //layout.on({ type: "hide", execute: "after" }, () => { Global.coqDocument.recenterEditor(); });
  //layout.on({ type: "show", execute: "after" }, () => { Global.coqDocument.recenterEditor(); });

  const toolbarStreams = setupToolbar();
  const shortcutsStreams = setupKeybindings();
  const userActionStreams = setupUserActions(toolbarStreams, shortcutsStreams);

  userActionStreams.loadedFile$.subscribe(() => Global.coqDocument.contextPanel.clear());

  interface GoToPositions {
    destinationPos: AceAjax.Position;
    lastEditStopPos: AceAjax.Position;
  }
  const [forwardGoTo$, backwardGoTo$] = userActionStreams.goTo$
    // filter out when position is already reached
    .flatMap<GoToPositions>(() => {
      const lastEditStopPos = Global.coqDocument.getLastEditStop();
      const destinationPos = Global.coqDocument.editor.getCursorPosition();
      return (
        _.isEqual(lastEditStopPos, destinationPos)
          ? []
          : [{ destinationPos: destinationPos, lastEditStopPos: lastEditStopPos, }]
      );
    })
    // partition on the direction of the goTo
    .partition(o => isBefore(Strictly.Yes, o.lastEditStopPos, o.destinationPos));

  const editAtFromBackwardGoTo$ = backwardGoTo$
    .flatMap(o => {
      const maybeEdit = Global.coqDocument.getEditAtPosition(o.destinationPos);
      return (
        maybeEdit
          .bind(e => e.getPreviousStateId())
          .fmap(s => new CoqtopInput.EditAt(s)).caseOf({
            nothing: () => [],
            just: i => [i],
          })
      );
    })
    .share();

  Coq85.setupSyntaxHovering();
  tabsAreReadyPromise.then(Theme.setupTheme);
  Theme.afterChange$.subscribe(() => onResize());
  // These also help with the initial display...
  Theme.afterChange$.subscribe(() => { rightLayout.refresh(); });
  Theme.afterChange$.subscribe(() => { bottomLayout.refresh(); });

  const nextSubject = new Rx.ReplaySubject(1);
  userActionStreams.next$.subscribe(() => nextSubject.onNext({}));

  const editsToProcessStream =
    Coq85.onNextReactive(Global.coqDocument, nextSubject.asObservable());

  const previousEditToReach$: Rx.Observable<ISentence<IProcessed>> =
    userActionStreams.prev$
      .flatMap(() => listFromMaybe(Global.coqDocument.getLastEdit()))
      .flatMap(e => listFromMaybe(e.previousEdit))
      .filter(e => e.stage instanceof Edit.Processed);

  const editAtBecausePrev$ =
    previousEditToReach$
      .map(e => new CoqtopInput.EditAt(e.stage.stateId));

  /*
  Will have just(pos) when we are trying to reach some position, and
  nothing() when we are not.
  */
  const forwardGoToSubject = new Rx.Subject<Maybe<AceAjax.Position>>();
  forwardGoTo$.subscribe(o => forwardGoToSubject.onNext(just(o.destinationPos)));

  //editsToProcessStream.subscribe(e => Global.coqDocument.pushEdit(e));
  //editsToProcessStream.subscribe(e => Global.coqDocument.moveCursorToPositionAndCenter(e.getStopPosition()));
  const addsToProcessStream = Coq85.processEditsReactive(editsToProcessStream);

  // TODO: I don't like how I pass queriesObserver to each edit stage, I should
  // improve on this design
  const queriesSubject = new Rx.Subject<ICoqtopInput>();
  const queriesObserver = queriesSubject.asObserver();
  const queries$ = queriesSubject.asObservable();

  const coqtopOutput$s = Coqtop.setupCoqtopCommunication([
    // reset Coqtop when a file is loaded
    userActionStreams.loadedFile$
      .startWith({}) // also do it on loading the page
      .flatMap(() => [
        new CoqtopInput.EditAt(1),
        new CoqtopInput.AddPrime("Require Import PeaCoq.PeaCoq."),
      ]),
    addsToProcessStream,
    editAtBecauseEditorChange,
    editAtFromBackwardGoTo$,
    queries$,
    editAtBecausePrev$,
  ]);

  const nextBecauseGoTo$ = setupUserInteractionForwardGoto(
    forwardGoTo$.map(goto => goto.destinationPos),
    Global.coqDocument.edits.editCreated$,
    coqtopOutput$s.feedback$s.errorMsg$
  );

  nextBecauseGoTo$
    .delay(0) // this is needed to set up the feedback properly
    .subscribe(() => nextSubject.onNext({}));

  coqtopOutput$s.feedback$s.processed$
    .subscribe(f => {
      if (f.editOrState === "state") {
        const stateId = f.editOrStateId;
        const editsBeingProcessed = Global.coqDocument.getEditsBeingProcessed();
        const edit = _(editsBeingProcessed).find(e => e.stage.stateId === stateId);
        if (edit) {
          const newStage = new Edit.Processed(edit.stage, queriesObserver);
          edit.setStage(newStage);
          // if (
          //   Global.coqDocument.getEditsToProcess().length === 0
          //   && Global.coqDocument.getEditsBeingProcessed().length === 0
          // ) {
          //   Global.coqDocument.moveCursorToPositionAndCenter(edit.stopPosition);
          // }
        }
      } else {
        debugger; // not sure this ever happens
      }
    });

  // Logging feedbacks that I haven't figured out what to do with yet
  subscribeAndLog(
    coqtopOutput$s.feedback$
      .filter(f => !(f.feedbackContent instanceof FeedbackContent.FileDependency))
      .filter(f => !(f.feedbackContent instanceof FeedbackContent.FileLoaded))
      .filter(f => !(f.feedbackContent instanceof FeedbackContent.AddedAxiom))
      .filter(f => !(f.feedbackContent instanceof FeedbackContent.Processed && f.editOrState === "state"))
      .filter(f => !(f.feedbackContent instanceof FeedbackContent.ProcessingIn && f.editOrState === "state"))
      .filter(f => !(f.feedbackContent instanceof FeedbackContent.ErrorMsg))
      .distinctUntilChanged()
  );

  // coqtopOutput$s.feedback$
  //   .filter(f => f.feedbackContent instanceof FeedbackContent.ErrorMsg)
  //   .distinctUntilChanged()
  //   .subscribe(f => {
  //     const e = <FeedbackContent.ErrorMsg><any>f.feedbackContent;
  //     assert(f.editOrState === "state", "Expected ErrorMsg to carry a state, not an edit");
  //     const failedStateId = f.editOrStateId;
  //     const failedEditStage = _(Global.coqDocument.getEditStagesBeingProcessed()).find(s => s.stateId === failedStateId);
  //     if (failedEditStage) {
  //       const failedEdit = failedEditStage.edit;
  //       Global.coqDocument.removeEditAndFollowingOnes(failedEdit);
  //       Global.tabs.errors.setValue(e.message, true);
  //       const errorStart = Global.coqDocument.movePositionRight(failedEdit.getStartPosition(), e.start);
  //       const errorStop = Global.coqDocument.movePositionRight(failedEdit.getStartPosition(), e.stop);
  //       const errorRange = new AceAjax.Range(errorStart.row, errorStart.column, errorStop.row, errorStop.column);
  //       Global.coqDocument.markError(errorRange);
  //     }
  //   });

  const editorError$: Rx.Observable<IEditorError> =
    coqtopOutput$s.valueFail$
      .map(vf => pimpMyError(vf))
      .share();

  editorError$.subscribe(ee =>
    Global.coqDocument.removeEditAndFollowingOnes(ee.failedEdit)
  );

  new CoqtopPanel(
    $(w2ui[rightLayoutName].get("bottom").content),
    coqtopOutput$s.feedback$s.errorMsg$,
    coqtopOutput$s.message$
  );

  editorError$.subscribe(ee => ee.range.fmap(range =>
    Global.coqDocument.markError(range)
  ));

  editorError$.subscribe(ee =>
    // so, apparently we won't receive feedbacks for the edits before this one
    // so we need to mark them all processed...
    _(Global.coqDocument.getEditsBeingProcessed())
      // ASSUMPTION: state IDs are assigned monotonically
      .filter(e => e.stage.stateId < ee.error.stateId)
      .each(_ => { debugger; })
      .each(e => e.setStage(new Edit.Processed(e.stage, queriesObserver)))
  );

  setupTextCursorPositionUpdate(
    Global.coqDocument.edits.editProcessed$,
    editorError$,
    previousEditToReach$,
    editsToProcessStream
  );

  coqtopOutput$s.valueGood$s.editAt$
    .subscribe(r => {
      const processedEdits = Global.coqDocument.getProcessedEdits();
      const firstEditAfter =
        _(processedEdits).find(e => e.stage.stateId > (<CoqtopInput.EditAt>r.input).stateId);
      if (firstEditAfter) {
        Global.coqDocument.removeEditAndFollowingOnes(firstEditAfter);
      }
    });

  // I'm not sure when this happens, for now I'll assume it doesn't
  coqtopOutput$s.valueGood$s.editAt$
    .subscribe(io => {
      if (io.output.response.contents.hasOwnProperty("Right")) { throw io; }
    });

  // outputFromEditAt$
  //   .subscribe(r => proofTreeOnEditAt(
  //     hideProofTreePanel,
  //     r.input.getArgs()
  //   ));

  // Global.coqDocument.edits.editProcessed$
  //   .flatMap(e =>
  //     e.stage.getContext()
  //       .then(c => ({
  //         edit: e,
  //         context: c,
  //       }))
  //   )
  // .subscribe(({ edit, context }) => {
  //   // TODO: gotta find a way to know how status length evolved
  //   proofTreeOnEdit(
  //     showProofTreePanel,
  //     hideProofTreePanel,
  //     edit.query,
  //     edit.stage.stateId,
  //     context
  //   );
  // });

});

// const lastStatus: IStatus;

// function editorOnEditAt(sid: number) {
//   const edit = _(Global.coqDocument.editsProcessed).find(e => e.stateId === sid);
//   if (edit) {
//     killEditsAfterPosition(Global.coqDocument, edit.getStopPosition());
//     updateCoqtopTabs(edit.goals, edit.context);
//   }
// }

// function proofTreeOnStatus(s) {
//   lastStatus = s;
// }

function updateCoqtopTabs(context: PeaCoqContext) {
  console.log("TODO: updateCoqtopTabs");
  // clearCoqtopTabs(false);
  // if (context.length > 0) {
  //   pretty.div.append(context[0].getHTML());
  //   foreground.setValue(goals.fgGoals[0].toString(), false);
  // }
}

export function onResize(): void {
  Global.coqDocument.editor.resize();
  getActiveProofTree().fmap(t => {
    const parent = $("#prooftree").parent();
    t.resize(parent.width(), parent.height());
  });
}

function showProofTreePanel(): Promise<{}> {
  return new Promise(function(onFulfilled) {
    const handler = function(event: W2UI.W2Event) {
      event.onComplete = onFulfilled;
      bottomLayout.off("show", handler);
    };
    bottomLayout.on("show", handler);
    layout.set("bottom", { size: "30%" });
    bottomLayout.show("top");
  });
}

function hideProofTreePanel(): void {
  layout.set("bottom", { size: "20px" });
  bottomLayout.hide("top");
}

function updateFontSize(d: ICoqDocument): void {
  d.editor.setOption("fontSize", fontSize);
  Global.coqDocument.contextPanel.onFontSizeChanged(fontSize);
  jss.set("#pretty-content", { "font-size": fontSize + "px" });
  jss.set("svg body", { "font-size": fontSize + "px" });
  getActiveProofTree().fmap(t => t.update());
}

function setupW2LayoutResizeStream(layout: W2UI.W2Layout): Rx.Observable<{}> {
  return Rx.Observable
    .create(observer => {
      layout.on({ type: "resize", execute: "after" }, () => observer.onNext({}));
    })
    .share()
    ;
}

interface UserActionStreams {
  goTo$: Rx.Observable<{}>,
  loadedFile$: Rx.Observable<{}>,
  next$: Rx.Observable<{}>,
  prev$: Rx.Observable<{}>,
}

function setupUserActions(
  toolbarStreams: ToolbarStreams,
  shortcutsStreams: ShortcutsStreams
): UserActionStreams {
  const fontDecreasedStream =
    Rx.Observable
      .merge(toolbarStreams.fontDecrease, shortcutsStreams.fontDecrease)
      .do(() => { fontSize--; })
      .share();
  const fontIncreasedStream =
    Rx.Observable
      .merge(toolbarStreams.fontIncrease, shortcutsStreams.fontIncrease)
      .do(() => { fontSize++; })
      .share();
  Rx.Observable
    .merge(fontIncreasedStream, fontDecreasedStream)
    .subscribe(() => { updateFontSize(Global.coqDocument); });
  const goTo$ = Rx.Observable
    .merge(toolbarStreams.goToCaret, shortcutsStreams.goToCaret);
  const next$ = Rx.Observable
    .merge(toolbarStreams.next, shortcutsStreams.next);
  const prev$ = Rx.Observable
    .merge(toolbarStreams.previous, shortcutsStreams.previous);
  Rx.Observable
    .merge(toolbarStreams.load, shortcutsStreams.load)
    .subscribe(pickFile);
  Rx.Observable
    .merge(toolbarStreams.save, shortcutsStreams.save)
    .subscribe(saveFile);
  const loadedFilesStream = setupLoadFile();
  setupSaveFile();
  return {
    goTo$: goTo$,
    loadedFile$: loadedFilesStream,
    next$: next$,
    prev$: prev$,
  };
}

function minPos(pos1: AceAjax.Position, pos2: AceAjax.Position): AceAjax.Position {
  if (pos1.row < pos2.row) {
    return pos1;
  }
  if (pos2.row < pos1.row) {
    return pos2;
  }
  if (pos1.column < pos2.column) {
    return pos1;
  }
  return pos2;
}

function mapCursorPositionToContext(
  pos$: Rx.Observable<AceAjax.Position>
): Rx.Observable<PeaCoqContext> {

  /* nothing() if no edit to display, just(edit) if there is one */
  const editToBeDisplayed$: Rx.Observable<Maybe<ISentence<IEditStage>>> =
    pos$
      .map(pos => {
        // we want to display the last edit whose stopPos is before `pos`
        const edit = _(Global.coqDocument.getAllEdits())
          .findLast(s => isBefore(Strictly.No, s.stopPosition, pos));
        return edit ? just(edit) : nothing();
      })
      .distinctUntilChanged();

  if (DebugFlags.editToBeDisplayed) { subscribeAndLog(editToBeDisplayed$); }

  return editToBeDisplayed$
    .flatMapLatest(edit => edit.caseOf({
      nothing: () => Promise.resolve(emptyContext),
      just: e => e.getProcessedStage().then(s => s.getContext()),
    }));

}
