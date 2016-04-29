import * as FeedbackContent from "./coq/feedback-content";

import * as Coq85 from "./editor/coq85";
import { CoqDocument } from "./editor/coq-document";
import * as Edit from "./editor/edit";
import { clearEdit, displayEdit, setupEditor } from "./editor/editor";
import { EditorTab } from "./editor/editor-tab";
import { isBefore } from "./editor/editor-utils";
import { setupKeybindings } from "./editor/keybindings";
import { setupProgressBar } from "./editor/progress-bar";
import { Tab } from "./editor/tab";
// // TODO: toolbar.ts should setup{Load,Save}File upon setupToolbar
// // TODO: unless it can't because of keybindings?
import { pickFile, saveFile, setupLoadFile, setupToolbar, setupSaveFile } from "./editor/toolbar";

// TODO: not sure if this file should be creating those nodes...
import { GoalNode } from "./prooftree/goalnode";
import { ProofTree, proofTrees } from "./prooftree/prooftree";
import { Tactic } from "./prooftree/tactic";
import { TacticGroupNode } from "./prooftree/tacticgroupnode";
import { getActiveProofTree } from "./prooftree/utils";

import * as Coqtop from "./coqtop-rx";
import * as CoqtopInput from "./coqtop-input";
import * as Global from "./global-variables";
import { Goals } from "./goals";
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
  const editorCursorChangeStream = Rx.Observable
    .create((observer) => {
      editor.selection.on("changeCursor", (e) => { observer.onNext(e); });
    })
    .share();

  const editorCursorPositionStream = editorCursorChangeStream
    .map(() => editor.selection.getCursor());

  const editToBeDisplayed$: Rx.Observable<IEdit<IProcessed>> =
    editorCursorPositionStream
      .flatMap(pos => {
        // we want to display the last edit whose stopPos is before `pos`
        let edit = _(Global.coqDocument.getProcessedEdits())
          .findLast((s) => isBefore(Strictly.No, s.stopPosition, pos));
        // if no edit, we should display the last edit before the cursor
        if (!edit) { edit = _(Global.coqDocument.getProcessedEdits()).last(); }
        return edit ? [edit] : [];
      })
      .distinctUntilChanged();

  editToBeDisplayed$
    .flatMapLatest(edit => {
      const stage = edit.stage;
      const contextPromise = stage.getContext();
      const goalsPromise = stage.getGoals();
      return Rx.Observable.fromPromise(Promise.all<any>([contextPromise, goalsPromise]));
    })
    .subscribe(([context, goals]) => displayEdit(context, goals));

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
      { type: "bottom", size: "50%", resizable: true, tabs: { tabs: [], } },
    ],
  });

  $().w2layout({
    name: bottomLayoutName,
    panels: [
      { type: "top", hidden: true, resizable: false, content: $("<div>", { id: "prooftree" }) },
      { type: "main", size: "20px", overflow: "hidden", resizable: false, content: $("<div>", { id: "progress-bar", style: "height: 100%" }) },
    ],
  });

  layout = w2ui["layout"];
  const rightLayout = w2ui[rightLayoutName];
  bottomLayout = w2ui[bottomLayoutName];
  const contextTabs = w2ui[rightLayoutName + "_main_tabs"];
  contextTabs.onClick = function(event) { $("#myTabsContent").html(event.target); };
  const coqtopTabs = w2ui[rightLayoutName + "_bottom_tabs"];

  bottomLayout.on({ type: "render", execute: "after" }, () => {
    setupProgressBar();
    bottomLayout.refresh();
  });

  // Rx.Observable.interval(1000)
  //   .map(n => n%2 === 0)
  //   .subscribe(b => b ? showProofTreePanel() : hideProofTreePanel());

  const rightLayoutRenderedStream = Rx.Observable
    .create((observer) => {
      rightLayout.on({ type: "render", execute: "after" }, () => observer.onNext({}));
    })
    .share();

  const tabsAreReadyPromise = new Promise((onFulfilled) => {
    rightLayoutRenderedStream.take(1).subscribe(() => {

      const tabs: ITabs = <any>{};

      // top panes
      tabs.pretty = new Tab("pretty", "Pretty", rightLayoutName, "main");
      tabs.pretty.div.css("padding-left", "4px");
      tabs.foreground = new EditorTab("foreground", "Foreground", rightLayoutName, "main");
      tabs.background = new EditorTab("background", "Background", rightLayoutName, "main");
      tabs.shelved = new EditorTab("shelved", "Shelved", rightLayoutName, "main");
      tabs.givenUp = new EditorTab("givenup", "Given up", rightLayoutName, "main");

      contextTabs.click("pretty");

      // bottom panes
      tabs.notices = new EditorTab("notices", "Notices", rightLayoutName, "bottom");
      tabs.warnings = new EditorTab("warnings", "Warnings", rightLayoutName, "bottom");
      tabs.errors = new EditorTab("errors", "Errors", rightLayoutName, "bottom");
      tabs.infos = new EditorTab("infos", "Infos", rightLayoutName, "bottom");
      tabs.debug = new EditorTab("debug", "Debug", rightLayoutName, "bottom");
      tabs.failures = new EditorTab("failures", "Failures", rightLayoutName, "bottom");
      // tabs.feedback = new EditorTab("feedback", "Feedback", rightLayoutName, "bottom");
      tabs.jobs = new EditorTab("jobs", "Jobs", rightLayoutName, "bottom");

      coqtopTabs.click("notices");

      Global.setTabs(tabs);

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
  Rx.Observable.merge(windowResizeStream, layoutResizeStream, rightLayoutResizeStream)
    // only fire once every <resizeBufferingTime> milliseconds
    .bufferWithTime(resizeBufferingTime).filter((a) => !_.isEmpty(a))
    .subscribe(onResize)
    ;

  // TODO: this is probably needed so that the main editor stays centered
  // when the prooftree panel showsup or hides
  //layout.on({ type: "hide", execute: "after" }, () => { Global.coqDocument.recenterEditor(); });
  //layout.on({ type: "show", execute: "after" }, () => { Global.coqDocument.recenterEditor(); });

  const toolbarStreams = setupToolbar();
  const shortcutsStreams = setupKeybindings();
  const userActionStreams = setupUserActions(toolbarStreams, shortcutsStreams);

  userActionStreams.loadedFile$.subscribe(() => clearEdit());

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

  const nextSubject = new Rx.Subject<{}>();
  userActionStreams.next$.subscribe(() => nextSubject.onNext({}));

  const editsToProcessStream =
    Coq85.onNextReactive(Global.coqDocument, nextSubject.asObservable());

  /*
  Will have just(pos) when we are trying to reach some position, and
  nothing() when we are not.
  */
  const forwardGoToSubject = new Rx.Subject<Maybe<AceAjax.Position>>();
  forwardGoTo$.subscribe(o => forwardGoToSubject.onNext(just(o.destinationPos)));
  const nextBecauseGoTo$ = Rx.Observable
    .combineLatest(
    forwardGoToSubject.asObservable(),
    // TODO: this won't work on reload...
    Global.coqDocument.edits.change$
      .map(() => Global.coqDocument.getLastEditStop())
      .startWith({ row: 0, column: 0 }) // otherwise it doesn't fire before first change
    )
    .flatMap(([m, eStopPos]) => {
      return m.caseOf({
        nothing: () => [],
        just: destinationPos => {
          // we need to continue if both:
          // 1. eStopPos < destinationPos
          // 2. the range [eStopPos, destinationPos] contains some text
          const cond1 = isBefore(Strictly.Yes, eStopPos, destinationPos);
          const range = AceAjax.Range.fromPoints(eStopPos, destinationPos);
          const text = Global.coqDocument.session.getDocument().getTextRange(range);
          const cond2 = CoqStringUtils.coqTrimLeft(text) !== "";
          if (cond1 && cond2) {
            // need another next
            return [{}];
          } else {
            // don't need another next
            forwardGoToSubject.onNext(nothing());
            return [];
          }
        },
      });
    });
  nextBecauseGoTo$.subscribe(() => nextSubject.onNext({}));

  //editsToProcessStream.subscribe((e) => Global.coqDocument.pushEdit(e));
  //editsToProcessStream.subscribe((e) => Global.coqDocument.moveCursorToPositionAndCenter(e.getStopPosition()));
  const addsToProcessStream = Coq85.processEditsReactive(editsToProcessStream);

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
  ]);

  coqtopOutput$s.feedback$
    .filter(f => f.feedbackContent instanceof FeedbackContent.Processed)
    .subscribe(f => {
      if (f.editOrState === "state") {
        const stateId = f.editOrStateId;
        const editsBeingProcessed = Global.coqDocument.getEditsBeingProcessed();
        const edit = _(editsBeingProcessed).find(e => e.stage.stateId === stateId);
        if (edit) {
          const newStage = new Edit.Processed(edit.stage, queriesObserver);
          const newEdit = edit.setStage(newStage);
          if (
            Global.coqDocument.getEditsToProcess().length === 0
            && Global.coqDocument.getEditsBeingProcessed().length === 0
          ) {
            Global.coqDocument.moveCursorToPositionAndCenter(newEdit.stopPosition);
          }
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
  //   .filter((f) => f.feedbackContent instanceof FeedbackContent.ErrorMsg)
  //   .distinctUntilChanged()
  //   .subscribe((f) => {
  //     const e = <FeedbackContent.ErrorMsg><any>f.feedbackContent;
  //     assert(f.editOrState === "state", "Expected ErrorMsg to carry a state, not an edit");
  //     const failedStateId = f.editOrStateId;
  //     const failedEditStage = _(Global.coqDocument.getEditStagesBeingProcessed()).find((s) => s.stateId === failedStateId);
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

  coqtopOutput$s.error$
    .subscribe((e) => {
      const failedEdit = Global.coqDocument.getEditsBeingProcessed()[0];
      Global.coqDocument.removeEditAndFollowingOnes(failedEdit);
      Global.tabs.errors.setValue(e.message, true);
      e.location.fmap((loc) => {
        const errorStart = Global.coqDocument.movePositionRight(failedEdit.startPosition, loc.startPos);
        const errorStop = Global.coqDocument.movePositionRight(failedEdit.startPosition, loc.stopPos);
        const errorRange = new AceAjax.Range(errorStart.row, errorStart.column, errorStop.row, errorStop.column);
        Global.coqDocument.markError(errorRange);
      });
    });

  coqtopOutput$s.response$
    .filter(r => r.input instanceof CoqtopInput.EditAt)
    .subscribe(r => {
      const processedEdits = Global.coqDocument.getProcessedEdits();
      const firstEditAfter =
        _(processedEdits).find(e => e.stage.stateId > (<CoqtopInput.EditAt>r.input).stateId);
      if (firstEditAfter) {
        Global.coqDocument.removeEditAndFollowingOnes(firstEditAfter);
      }
    });

});

// const lastStatus: IStatus;

// function editorOnEditAt(sid: number) {
//   const edit = _(Global.coqDocument.editsProcessed).find((e) => e.stateId === sid);
//   if (edit) {
//     killEditsAfterPosition(Global.coqDocument, edit.getStopPosition());
//     updateCoqtopTabs(edit.goals, edit.context);
//   }
// }

// function proofTreeOnStatus(s) {
//   lastStatus = s;
// }

function updateCoqtopTabs(goals: IGoals, context: PeaCoqContext) {
  console.log("TODO: updateCoqtopTabs");
  // clearCoqtopTabs(false);
  // if (context.length > 0) {
  //   pretty.div.append(context[0].getHTML());
  //   foreground.setValue(goals.fgGoals[0].toString(), false);
  // }
}

// function proofTreeOnEdit(
//   query: string,
//   stateId: number,
//   lastStatus: IStatus,
//   status: IStatus,
//   goals: IGoals,
//   context: PeaCoqContext
// ): void {
//
//   const trimmed = CoqStringUtils.coqTrim(query);
//
//   updateCoqtopTabs(goals, context);
//
//   if (
//     lastStatus.statusAllProofs.length + 1 === status.statusAllProofs.length
//     &&
//     proofTrees.length + 1 === status.statusAllProofs.length
//   ) {
//     // we are behind on the number of proof trees, create one
//     showProofTreePanel()
//       .then(() => { // needs to be before for width/height
//         const pt = new ProofTree(
//           status.statusProofName,
//           $("#prooftree")[0],
//           $("#prooftree").parent().width(),
//           $("#prooftree").parent().height()
//         );
//         proofTrees.unshift(pt);
//         assert(context.length === 1, "proofTreeOnGetContext: c.length === 1, c.length: " + context.length);
//         const g = new GoalNode(pt, nothing(), goals, context[0]);
//         assert(pt.rootNode !== undefined, "proofTreeOnGetContext: new GoalNode should set rootNode");
//         g.stateIds.push(stateId);
//         pt.curNode = g;
//         pt.update();
//       });
//     return;
//   } else {
//     // multiple trees might have been finished at once?
//     while (proofTrees.length > status.statusAllProofs.length) {
//       proofTrees.shift();
//       if (proofTrees.length === 0) {
//         $("#prooftree").empty();
//         hideProofTreePanel();
//       }
//     }
//   }
//
//   if (proofTrees.length === 0) { return; }
//
//   const activeProofTree = proofTrees[0];
//   const curNode = activeProofTree.curNode;
//
//   if (isUpperCase(trimmed[0]) || CoqStringUtils.isBullet(trimmed)) {
//     curNode.goals = goals;
//     curNode.stateIds.push(stateId);
//     return;
//   }
//
//   let tactic: Tactic = _.find(curNode.getTactics(), (t) => t.tactic === trimmed);
//
//   const tacticGroup: ITacticGroupNode = (
//     tactic
//       ? tactic.parentGroup
//       : new TacticGroupNode(activeProofTree, curNode, "")
//   );
//
//   /*
//   We need to figure out which foreground goals are relevant to this tactic node.
//   If the number of unfocused goals has changed by running the tactic, the tactic
//   must have solved the previous goal and the current foreground goals are the
//   remaining ones.
//   Otherwise, the delta foreground goals have been created by running the tactic.
//   */
//   const goalsBefore = curNode.goals;
//   const goalsAfter = goals;
//   const nbRelevantGoals =
//     goalsBefore.bgGoals.length === goalsAfter.bgGoals.length
//       ? goalsAfter.fgGoals.length - (goalsBefore.fgGoals.length - 1)
//       : 0;
//   const relevantGoals = context.slice(0, nbRelevantGoals);
//
//   const goalNodes: IGoalNode[] =
//     _(relevantGoals).map(function(goal) {
//       return new GoalNode(
//         activeProofTree,
//         just(tacticGroup),
//         goals,
//         goal
//       );
//     }).value();
//
//   if (!tactic) {
//     curNode.tacticGroups.push(tacticGroup);
//     tactic = new Tactic(trimmed, tacticGroup, goalNodes);
//     tacticGroup.tactics.push(tactic);
//   } else {
//     tactic.goals = goalNodes;
//   }
//
//   tacticGroup.isProcessed = true;
//
//   if (goalNodes.length > 0) {
//     const curGoal: IGoalNode = goalNodes[0];
//     curGoal.stateIds.push(stateId);
//     activeProofTree.curNode = curGoal;
//     activeProofTree.update();
//   } else {
//     curNode.onChildSolved(stateId);
//   }
//
// }

/*
  For now, let"s just rewind within the tree or give up. Eventually,
  we could rewind into old trees.
 */
// function proofTreeOnEditAt(sid: number): void {
//
//   if (proofTrees.length === 0) { return; }
//   const activeProofTree = proofTrees[0];
//   //lastStateId = sid;
//   const curNode = activeProofTree.curNode;
//
//   // clean up necessary for tactics waiting
//   activeProofTree.tacticWaiting = nothing();
//
//   // first, get rid of all stored stateIds > sid
//   // and mark their children tactic groups unprocessed
//   const allGoals = activeProofTree.rootNode.getAllGoalDescendants();
//   _(allGoals).each((g) => {
//     if (_(g.stateIds).some((s) => s >= sid)) {
//       _(g.tacticGroups).each((g) => { g.isProcessed = false; });
//     }
//     g.stateIds = _(g.stateIds).filter((s) => s <= sid).value();
//   });
//   const target = _(allGoals).find((g) => {
//     return _(g.stateIds).some((s) => s === sid);
//   });
//   if (target) {
//     activeProofTree.curNode = target;
//     activeProofTree.update();
//   } else {
//     proofTrees.length = 0;
//     hideProofTreePanel();
//     $("#prooftree").empty();
//   }
//
// }

export function onResize(): void {
  Global.coqDocument.editor.resize();
  _(Global.getAllEditorTabs()).each((e) => e.resize());
  getActiveProofTree().fmap((t) => {
    const parent = $("#prooftree").parent();
    t.resize(parent.width(), parent.height());
  });
}

function hideProofTreePanel(): void {
  layout.set("bottom", { size: "20px" });
  bottomLayout.hide("top");
}

function showProofTreePanel(): Promise<{}> {
  return new Promise(function(onFulfilled) {
    const handler = function(event) {
      event.onComplete = onFulfilled;
      bottomLayout.off("show", handler);
    };
    bottomLayout.on("show", handler);
    layout.set("bottom", { size: "30%" });
    bottomLayout.show("top");
  });
}

function updateFontSize(d: ICoqDocument): void {
  d.editor.setOption("fontSize", fontSize);
  _(Global.getAllEditorTabs()).each((e: EditorTab) => {
    e.setOption("fontSize", fontSize);
  });
  jss.set("#pretty-content", { "font-size": fontSize + "px" });
  jss.set("svg body", { "font-size": fontSize + "px" });
  getActiveProofTree().fmap((t) => t.update());
}

function setupW2LayoutResizeStream(layout: W2UI.W2Layout): Rx.Observable<{}> {
  return Rx.Observable
    .create((observer) => {
      layout.on({ type: "resize", execute: "after" }, () => observer.onNext({}));
    })
    .share()
    ;
}

interface UserActionStreams {
  goTo$: Rx.Observable<{}>,
  loadedFile$: Rx.Observable<{}>,
  next$: Rx.Observable<{}>,
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
