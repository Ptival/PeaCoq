import * as Coq85 from "./editor/coq85";
import { CoqDocument } from "./editor/coq-document";
import * as Coqtop from "./coqtop-rx";
import * as CoqtopInput from "./coqtop-input";
import * as EditStage from "./editor/edit-stage";
import { displayEdit, setupEditor } from "./editor/editor";
import { EditorTab } from "./editor/editor-tab";
import * as FeedbackContent from "./coq/feedback-content";
import * as Global from "./global-variables";
// TODO: not sure if this file should be creating those nodes...
import { GoalNode } from "./prooftree/goalnode";
import { Goals } from "./goals";
import { setupKeybindings } from "./editor/keybindings";
import { PeaCoqGoal } from "./peacoq-goal";
import { setupProgressBar } from "./editor/progress-bar";
import { ProofTree, proofTrees } from "./prooftree/prooftree";
import { getActiveProofTree } from "./prooftree/utils";
import { Tab } from "./editor/tab";
import { Tactic } from "./prooftree/tactic";
import { TacticGroupNode } from "./prooftree/tacticgroupnode";
import * as Theme from "./theme";
// // TODO: toolbar.ts should setup{Load,Save}File upon setupToolbar
// // TODO: unless it can't because of keybindings?
import { pickFile, saveFile, setupLoadFile, setupToolbar, setupSaveFile } from "./editor/toolbar";

let fontSize = 16; // pixels
let resizeBufferingTime = 250; // milliseconds

// TODO: this should not be global
let layout: W2UI.W2Layout;
let bottomLayout: W2UI.W2Layout;
// let rightLayout: W2UI.W2Layout;
// let contextTabs: W2UI.W2Tabs;
// let coqtopTabs: W2UI.W2Tabs;

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

  let editor = ace.edit("editor");
  let editorCursorChangeStream = Rx.Observable
    .create((observer) => {
      editor.selection.on("changeCursor", (e) => { observer.onNext(e); });
    })
    .share();
  let editorCursorPositionStream = editorCursorChangeStream
    .map(() => editor.selection.getCursor());
  let readyEditUnderEditorCursorStream: Rx.Observable<IEdit> = editorCursorPositionStream
    .flatMap((pos) => {
      let stage = _(Global.coqDocument.getEditStagesReady())
        .find((stage) => stage.edit.containsPosition(pos));
      // if no edit, we should display the last edit before the cursor
      if (!stage) { stage = _(Global.coqDocument.getEditStagesReady()).last(); }
      return stage ? [stage.edit] : [];
    })
    .distinctUntilChanged();
  readyEditUnderEditorCursorStream.subscribe((edit) => {
    displayEdit(edit);
  });

  Global.setCoqDocument(new CoqDocument(editor));

  let editAtBecauseEditorChange: Rx.Observable<CoqtopInput.CoqtopInput> =
    Global.coqDocument.changeStream.flatMap((change) => {
      let maybeEdit = Global.coqDocument
        .getEditAtPosition(minPos(change.start, change.end));
      maybeEdit.fmap(e => Global.coqDocument.removeEditAndFollowingOnes(e));
      return maybeEdit.caseOf({
        nothing: () => [],
        just: e => [new CoqtopInput.EditAt(e.getPreviousStateId())]
      });
    });

  setupEditor(editor);
  editor.focus();

  let rightLayoutName = "right-layout";
  let bottomLayoutName = "bottom-layout";

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
  let rightLayout = w2ui[rightLayoutName];
  bottomLayout = w2ui[bottomLayoutName];
  let contextTabs = w2ui[rightLayoutName + "_main_tabs"];
  contextTabs.onClick = function(event) { $("#myTabsContent").html(event.target); };
  let coqtopTabs = w2ui[rightLayoutName + "_bottom_tabs"];

  bottomLayout.on({ type: "render", execute: "after" }, () => {
    setupProgressBar();
    bottomLayout.refresh();
  });

  // Rx.Observable.interval(1000)
  //   .map(n => n%2 === 0)
  //   .subscribe(b => b ? showProofTreePanel() : hideProofTreePanel());

  let rightLayoutRenderedStream = Rx.Observable
    .create((observer) => {
      rightLayout.on({ type: "render", execute: "after" }, () => observer.onNext({}));
    })
    .share();

  let tabsAreReadyPromise = new Promise((onFulfilled) => {
    rightLayoutRenderedStream.take(1).subscribe(() => {

      let tabs: ITabs = <any>{};

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

  let windowResizeStream: Rx.Observable<{}> = Rx.Observable.fromEvent($(window), "resize");
  let layoutResizeStream = setupW2LayoutResizeStream(layout);
  let rightLayoutResizeStream = setupW2LayoutResizeStream(rightLayout);
  Rx.Observable.merge(windowResizeStream, layoutResizeStream, rightLayoutResizeStream)
    // only fire once every <resizeBufferingTime> milliseconds
    .bufferWithTime(resizeBufferingTime).filter((a) => !_.isEmpty(a))
    .subscribe(onResize)
    ;

  // TODO: this is probably needed so that the main editor stays centered
  // when the prooftree panel showsup or hides
  //layout.on({ type: "hide", execute: "after" }, () => { Global.coqDocument.recenterEditor(); });
  //layout.on({ type: "show", execute: "after" }, () => { Global.coqDocument.recenterEditor(); });

  let toolbarStreams = setupToolbar();
  let shortcutsStreams = setupKeybindings();
  let userActionStreams = setupUserActions(toolbarStreams, shortcutsStreams);

  Coq85.setupSyntaxHovering();
  tabsAreReadyPromise.then(Theme.setupTheme);
  Theme.afterChange$.subscribe(() => onResize());
  // These also help with the initial display...
  Theme.afterChange$.subscribe(() => { rightLayout.refresh(); });
  Theme.afterChange$.subscribe(() => { bottomLayout.refresh(); });

  let editsToProcessStream = Coq85.onNextReactive(Global.coqDocument, userActionStreams.next);
  //editsToProcessStream.subscribe((e) => Global.coqDocument.pushEdit(e));
  //editsToProcessStream.subscribe((e) => Global.coqDocument.moveCursorToPositionAndCenter(e.getStopPosition()));
  let addsToProcessStream = Coq85.processEditsReactive(editsToProcessStream);

  let coqtopOutputStreams = Coqtop.setupCoqtopCommunication([
    // reset Coqtop when a file is loaded
    userActionStreams.loadedFile
      .startWith({})
      .flatMap(() => [
        new CoqtopInput.EditAt(1),
        new CoqtopInput.AddPrime("Require Import PeaCoq.PeaCoq.")
      ]),
    addsToProcessStream,
    editAtBecauseEditorChange,
  ]);

  // Disabled, see edit-stage.ts for reason why

  coqtopOutputStreams.goodResponse
    // keep only responses for adds produced by PeaCoq
    .filter((r) => r.input instanceof CoqtopInput.AddPrime && r.input.data !== undefined)
    .subscribe((r) => {
      let stateId = r.contents[0];
      let edit = r.input.data.edit;
      let stage = edit.stage;
      if (stage instanceof EditStage.ToProcess) {
        edit.stage = new EditStage.BeingProcessed(stage, stateId);
      }
    });

  coqtopOutputStreams.goodResponse
    .filter((r) => r.input instanceof CoqtopInput.Goal && r.input.data !== undefined)
    .subscribe((r) => {
      r.input.data.goals = new Goals(r.contents);
      // r.input.data.goals = goals;
      // let edit = r.input.data.edit;
      // let stage = edit.stage;
      // if (stage instanceof EditStage.BeingProcessed) {
      //   edit.stage = new EditStage.Ready(stage, goals);
      //   if (Global.coqDocument.getEditStagesToProcess().length === 0) {
      //     Global.coqDocument.moveCursorToPositionAndCenter(stage.getStopPosition());
      //   }
      // }
    });

  coqtopOutputStreams.goodResponse
    .filter((r) => r.input instanceof CoqtopInput.QueryPrime && r.input.data !== undefined)
    .subscribe((r) => {
      let edit = r.input.data.edit;
      let stage = edit.stage;
      let c = eval(<any>r.contents);
      // right now c will be [] if there is no context, or a one-element list
      let context = _(c).map((o) => new PeaCoqGoal(o.hyps, o.concl)).value();
      if (stage instanceof EditStage.BeingProcessed) {
        edit.stage = new EditStage.Ready(stage, r.input.data.goals, context);
        if (Global.coqDocument.getEditStagesToProcess().length === 0) {
          Global.coqDocument.moveCursorToPositionAndCenter(stage.getStopPosition());
        }
        displayEdit(edit);
      }
    });

  // Logging feedbacks that I haven't figured out what to do with yet
  subscribeAndLog(
    coqtopOutputStreams.feedback
      .filter((f) => !(f.feedbackContent instanceof FeedbackContent.FileDependency || f.feedbackContent instanceof FeedbackContent.FileLoaded))
      .filter((f) => !(f.feedbackContent instanceof FeedbackContent.AddedAxiom))
      .filter((f) => !(f.feedbackContent instanceof FeedbackContent.Processed && f.editOrState === "state"))
      .filter((f) => !(f.feedbackContent instanceof FeedbackContent.ProcessingIn && f.editOrState === "state"))
      .filter((f) => !(f.feedbackContent instanceof FeedbackContent.ErrorMsg))
  );

  coqtopOutputStreams.feedback
    .filter((f) => f.feedbackContent instanceof FeedbackContent.ErrorMsg)
    .distinctUntilChanged()
    .subscribe((f) => {
      let e = <FeedbackContent.ErrorMsg><any>f.feedbackContent;
      assert(f.editOrState === "state", "Expected ErrorMsg to carry a state, not an edit");
      let failedStateId = f.editOrStateId;
      let failedEditStage = _(Global.coqDocument.getEditStagesBeingProcessed()).find((s) => s.stateId === failedStateId);
      if (failedEditStage) {
        let failedEdit = failedEditStage.edit;
        Global.coqDocument.removeEditAndFollowingOnes(failedEdit);
        Global.tabs.errors.setValue(e.message, true);
        let errorStart = Global.coqDocument.movePositionRight(failedEdit.getStartPosition(), e.start);
        let errorStop = Global.coqDocument.movePositionRight(failedEdit.getStartPosition(), e.stop);
        let errorRange = new AceAjax.Range(errorStart.row, errorStart.column, errorStop.row, errorStop.column);
        Global.coqDocument.markError(errorRange);
      }
    });

});

// let lastStatus: IStatus;

// function editorOnEditAt(sid: number) {
//   let edit = _(Global.coqDocument.editsProcessed).find((e) => e.stateId === sid);
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

function proofTreeOnEdit(
  query: string,
  stateId: number,
  lastStatus: IStatus,
  status: IStatus,
  goals: IGoals,
  context: PeaCoqContext
): void {

  let trimmed = CoqStringUtils.coqTrim(query);

  updateCoqtopTabs(goals, context);

  if (
    lastStatus.statusAllProofs.length + 1 === status.statusAllProofs.length
    &&
    proofTrees.length + 1 === status.statusAllProofs.length
  ) {
    // we are behind on the number of proof trees, create one
    showProofTreePanel()
      .then(() => { // needs to be before for width/height
        let pt = new ProofTree(
          status.statusProofName,
          $("#prooftree")[0],
          $("#prooftree").parent().width(),
          $("#prooftree").parent().height()
        );
        proofTrees.unshift(pt);
        assert(context.length === 1, "proofTreeOnGetContext: c.length === 1, c.length: " + context.length);
        let g = new GoalNode(pt, nothing(), goals, context[0]);
        assert(pt.rootNode !== undefined, "proofTreeOnGetContext: new GoalNode should set rootNode");
        g.stateIds.push(stateId);
        pt.curNode = g;
        pt.update();
      });
    return;
  } else {
    // multiple trees might have been finished at once?
    while (proofTrees.length > status.statusAllProofs.length) {
      proofTrees.shift();
      if (proofTrees.length === 0) {
        $("#prooftree").empty();
        hideProofTreePanel();
      }
    }
  }

  if (proofTrees.length === 0) { return; }

  let activeProofTree = proofTrees[0];
  let curNode = activeProofTree.curNode;

  if (isUpperCase(trimmed[0]) || CoqStringUtils.isBullet(trimmed)) {
    curNode.goals = goals;
    curNode.stateIds.push(stateId);
    return;
  }

  let tactic: Tactic = _.find(curNode.getTactics(), (t) => t.tactic === trimmed);

  let tacticGroup: ITacticGroupNode = (
    tactic
      ? tactic.parentGroup
      : new TacticGroupNode(activeProofTree, curNode, "")
  );

  /*
  We need to figure out which foreground goals are relevant to this tactic node.
  If the number of unfocused goals has changed by running the tactic, the tactic
  must have solved the previous goal and the current foreground goals are the
  remaining ones.
  Otherwise, the delta foreground goals have been created by running the tactic.
  */
  let goalsBefore = curNode.goals;
  let goalsAfter = goals;
  let nbRelevantGoals =
    goalsBefore.bgGoals.length === goalsAfter.bgGoals.length
      ? goalsAfter.fgGoals.length - (goalsBefore.fgGoals.length - 1)
      : 0;
  let relevantGoals = context.slice(0, nbRelevantGoals);

  let goalNodes: IGoalNode[] =
    _(relevantGoals).map(function(goal) {
      return new GoalNode(
        activeProofTree,
        just(tacticGroup),
        goals,
        goal
      );
    }).value();

  if (!tactic) {
    curNode.tacticGroups.push(tacticGroup);
    tactic = new Tactic(trimmed, tacticGroup, goalNodes);
    tacticGroup.tactics.push(tactic);
  } else {
    tactic.goals = goalNodes;
  }

  tacticGroup.isProcessed = true;

  if (goalNodes.length > 0) {
    let curGoal: IGoalNode = goalNodes[0];
    curGoal.stateIds.push(stateId);
    activeProofTree.curNode = curGoal;
    activeProofTree.update();
  } else {
    curNode.onChildSolved(stateId);
  }

}

/*
  For now, let"s just rewind within the tree or give up. Eventually,
  we could rewind into old trees.
 */
function proofTreeOnEditAt(sid: number): void {

  if (proofTrees.length === 0) { return; }
  let activeProofTree = proofTrees[0];
  //lastStateId = sid;
  let curNode = activeProofTree.curNode;

  // clean up necessary for tactics waiting
  activeProofTree.tacticWaiting = nothing();

  // first, get rid of all stored stateIds > sid
  // and mark their children tactic groups unprocessed
  let allGoals = activeProofTree.rootNode.getAllGoalDescendants();
  _(allGoals).each((g) => {
    if (_(g.stateIds).some((s) => s >= sid)) {
      _(g.tacticGroups).each((g) => { g.isProcessed = false; });
    }
    g.stateIds = _(g.stateIds).filter((s) => s <= sid).value();
  });
  let target = _(allGoals).find((g) => {
    return _(g.stateIds).some((s) => s === sid);
  });
  if (target) {
    activeProofTree.curNode = target;
    activeProofTree.update();
  } else {
    proofTrees.length = 0;
    hideProofTreePanel();
    $("#prooftree").empty();
  }

}

export function onResize(): void {
  Global.coqDocument.editor.resize();
  _(Global.getAllEditorTabs()).each((e) => e.resize());
  getActiveProofTree().fmap((t) => {
    let parent = $("#prooftree").parent();
    t.resize(parent.width(), parent.height());
  });
}

function hideProofTreePanel(): void {
  layout.set("bottom", { size: "20px" });
  bottomLayout.hide("top");
}

function showProofTreePanel(): Promise<{}> {
  return new Promise(function(onFulfilled) {
    let handler = function(event) {
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
  loadedFile: Rx.Observable<{}>,
  next: Rx.Observable<{}>,
}

function setupUserActions(
  toolbarStreams: ToolbarStreams,
  shortcutsStreams: ShortcutsStreams
): UserActionStreams {
  let fontDecreasedStream =
    Rx.Observable
      .merge(toolbarStreams.fontDecrease, shortcutsStreams.fontDecrease)
      .do(() => { fontSize--; })
      .share();
  let fontIncreasedStream =
    Rx.Observable
      .merge(toolbarStreams.fontIncrease, shortcutsStreams.fontIncrease)
      .do(() => { fontSize++; })
      .share();
  Rx.Observable
    .merge(fontIncreasedStream, fontDecreasedStream)
    .subscribe(() => { updateFontSize(Global.coqDocument); });
  Rx.Observable
    .merge(toolbarStreams.goToCaret, shortcutsStreams.goToCaret)
    .subscribe(() => console.log("TODO: go to caret"));
  let nextStream = Rx.Observable
    .merge(toolbarStreams.next, shortcutsStreams.next);
  Rx.Observable
    .merge(toolbarStreams.previous, shortcutsStreams.previous)
    .subscribe(() => console.log("TODO: previous"));
  Rx.Observable
    .merge(toolbarStreams.load, shortcutsStreams.load)
    .subscribe(pickFile);
  Rx.Observable
    .merge(toolbarStreams.save, shortcutsStreams.save)
    .subscribe(saveFile);
  let loadedFilesStream = setupLoadFile();
  setupSaveFile();
  return {
    loadedFile: loadedFilesStream,
    next: nextStream,
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
