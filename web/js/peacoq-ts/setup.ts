import * as Context from "./editor/context";
import * as Goal from "./goal";
import * as Goals from "./goals";
import { walkJSON } from "./peacoq/json";

import * as Feedback from "./coq/feedback";
import * as FeedbackContent from "./coq/feedback-content";

import * as Coq85 from "./editor/coq85";
import { CoqDocument } from "./editor/coq-document";
import { CoqtopPanel } from "./editor/coqtop-panel";
import { ContextPanel } from "./editor/context-panel";
import * as Stage from "./editor/stage";
import * as Editor from "./editor/editor";

import { isBefore } from "./editor/editor-utils";
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
import { proofTreeOnEdit, onStmCanceled } from "./prooftree/prooftree-handlers";
import * as ProofTreeSetup from "./prooftree/setup";
import * as ProofTreeAutomation from "./prooftree/automation";

import * as Sertop from "./sertop";
import * as Command from "./sertop/command";
import * as ControlCommand from "./sertop/control-command";
import * as QueryCommand from "./sertop/query-command";

import * as DebugFlags from "./debug-flags";
import { PeaCoqGoal } from "./peacoq-goal";
import { Strictly } from "./strictly";
import * as Theme from "./theme";

import * as DisplayContext from "./editor/display-context";
import * as SentenceToDisplay from "./editor/sentence-to-display";
import * as UnderlineError from "./editor/underline-errors";
import * as Completion from "./editor/completion";

let fontSize = 16; // pixels
const resizeBufferingTime = 250; // milliseconds

// TODO: this should not be global
let layout: W2UI.W2Layout;
let bottomLayout: W2UI.W2Layout;
// const rightLayout: W2UI.W2Layout;
// const contextTabs: W2UI.W2Tabs;
// const coqtopTabs: W2UI.W2Tabs;

const peaCoqGetContextRouteId = 1;

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

  const doc: ICoqDocument = new CoqDocument(editor);

  const sentenceToDisplay$ = SentenceToDisplay.setup(doc);
  const stmObserve$ = DisplayContext.setup(doc, sentenceToDisplay$);

  // For now, if we don't remove the sentences immediately, when the user does
  // Next right after editing somewhere, the Next grabs the sentence after the
  // old tip, because the new tip has not registered yet. As a bad optimization,
  // we drop all sentences beyond the change immediately. This will be incorrect
  // when the user is allowed to edit within blocks.

  // Minor bug: this sends two Cancel commands when the user hits Enter
  // and Ace proceeds to insert a tabulation (these count as two changes)
  // The second Cancel is acknowledged by coqtop with no further action.
  const cancelBecauseEditorChange$: Rx.Observable<Rx.Observable<Command.Control<ISertop.IControlCommand.IStmCancel>>> =
    doc.editorChange$
      .flatMap<ISentence<IStage>>(change =>
        doc.getSentenceAtPosition(minPos(change.start, change.end)).caseOf({
          nothing: () => [],
          just: s => [s],
        })
      )
      .do(sRemoved => doc.removeSentences(s => s.sentenceId >= sRemoved.sentenceId))
      .flatMap(s =>
        s.getStateId()
        .caseOf({
          nothing: () => [],
          just: sid => [Rx.Observable.just(new Command.Control(new ControlCommand.StmCancel([sid])))],
        })
      )
      .share();

  Editor.setupMainEditor(doc, editor);

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
      { type: "top", size: "90%", overflow: "hidden", hidden: true, resizable: false, content: $("<div>", { id: "prooftree" }) },
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
    setupProgressBar(doc);
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

      doc.contextPanel = new ContextPanel(doc, rightLayoutName);

      // TODO: stream this
      updateFontSize(doc);

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

  resize$.subscribe(() => onResize(doc));
  resize$.subscribe(() => doc.contextPanel.onResize());

  const toolbarStreams = setupToolbar(doc);
  const shortcutsStreams = setupKeybindings(doc);
  const userActionStreams = setupUserActions(doc, toolbarStreams, shortcutsStreams);

  userActionStreams.loadedFile$.subscribe(() => doc.contextPanel.clear());

  interface GoToPositions {
    destinationPos: AceAjax.Position;
    lastEditStopPos: AceAjax.Position;
  }
  const [forwardGoTo$, backwardGoTo$] = userActionStreams.goTo$
    // filter out when position is already reached
    .flatMap<GoToPositions>(() => {
      const lastEditStopPos = doc.getLastSentenceStop();
      const destinationPos = doc.editor.getCursorPosition();
      return (
        _.isEqual(lastEditStopPos, destinationPos)
          ? []
          : [{ destinationPos: destinationPos, lastEditStopPos: lastEditStopPos, }]
      );
    })
    // partition on the direction of the goTo
    .partition(o => isBefore(Strictly.Yes, o.lastEditStopPos, o.destinationPos));

  const cancelFromBackwardGoTo$: CommandStream<any> =
    backwardGoTo$
      .flatMap(o => {
        const maybeSentence = doc.getSentenceAtPosition(o.destinationPos);
        return (
          maybeSentence
            .bind(e => e.getStateId())
            .fmap(s => new Command.Control(new ControlCommand.StmCancel([s])))
            .caseOf({
              nothing: () => [],
              just: cmd => [Rx.Observable.just(cmd)],
            })
        );
      })
      .share();

  Coq85.setupSyntaxHovering();
  tabsAreReadyPromise.then(() => Theme.setupTheme(doc));
  Theme.afterChange$.subscribe(() => onResize(doc));
  // These also help with the initial display...
  Theme.afterChange$.subscribe(() => { rightLayout.refresh(); });
  Theme.afterChange$.subscribe(() => { bottomLayout.refresh(); });

  const nextSubject = new Rx.ReplaySubject(1);
  userActionStreams.next$.subscribe(() => nextSubject.onNext({}));

  const sentencesToProcessStream = doc.nextSentence(nextSubject.asObservable());

  const sentenceToCancelBecausePrev$: Rx.Observable<ISentence<IStage>> =
    userActionStreams.prev$
      .flatMap(({}) => {
        if (doc.getSentencesToProcess().length > 0) { return []; }
        return [_.maxBy(doc.getAllSentences(), s => s.sentenceId)];
      })
      .share();

  sentenceToCancelBecausePrev$.subscribe(s => {
    doc.moveCursorToPositionAndCenter(s.startPosition);
  });

  const cancelBecausePrev$: CommandStream<any> =
    sentenceToCancelBecausePrev$
      .flatMap(s => {
        return s.getStateId().caseOf({
          nothing: () => [],
          just: sid => [Rx.Observable.just(new Command.Control(new ControlCommand.StmCancel([sid])))],
        });
      })
      .share();

  /*
  Will have just(pos) when we are trying to reach some position, and
  nothing() when we are not.
  */
  const forwardGoToSubject = new Rx.Subject<Maybe<AceAjax.Position>>();
  forwardGoTo$.subscribe(o => forwardGoToSubject.onNext(just(o.destinationPos)));

  sentencesToProcessStream.subscribe(e => doc.moveCursorToPositionAndCenter(e.stopPosition));

  const addsToProcess$: CommandStream<ISertop.IControl<ISertop.IControlCommand.IStmAdd>> =
    sentencesToProcessStream
      .map(s => {
        const command = new Command.Control(new ControlCommand.StmAdd({}, s.query, false));
        s.commandTag = just(command.tag);
        return Rx.Observable.just(command);
      })
      .share();

  // TODO: I don't like how I pass queriesObserver to each edit stage, I should
  // improve on this design
  const peaCoqGetContext$ = new Rx.Subject<ISertop.IControl<ISertop.IControlCommand.IStmQuery>>();

  // Here are subjects for observables that react to coqtop output
  const cancelBecauseErrorMsg$ = new Rx.Subject<CommandStreamItem<any>>();
  const queryForTacticToTry$ = new Rx.Subject<CommandStreamItem<any>>();

  const quitBecauseFileLoaded$: CommandStream<any> =
    userActionStreams.loadedFile$
      .startWith({}) // quit upon loading the webpage
      .map(({}) => Rx.Observable.just(new Command.Control(new ControlCommand.Quit())))
      .share();

  const inputsThatChangeErrorState$: CommandStream<any> =
    Rx.Observable.merge<CommandStreamItem<any>>([
      quitBecauseFileLoaded$,
      addsToProcess$,
      cancelBecauseEditorChange$,
      cancelBecausePrev$,
      cancelFromBackwardGoTo$,
    ]);

  const coqtopInputs$: CommandStream<any> =
    Rx.Observable.merge<CommandStreamItem<any>>([
      inputsThatChangeErrorState$,
      cancelBecauseErrorMsg$,
      stmObserve$,
      peaCoqGetContext$.map(i => Rx.Observable.just(i)),
      queryForTacticToTry$,
    ]);

  // Automated tasks need to stop whenever the user changes the current state
  const stopAutomationRound$: Rx.Observable<{}> =
    Rx.Observable.merge([
      quitBecauseFileLoaded$.map(_ => ({})),
      addsToProcess$.map(_ => ({})),
      cancelBecauseEditorChange$,
      cancelBecausePrev$,
      cancelFromBackwardGoTo$,
    ]);

  doc.editor.completers = [{ getCompletions: Completion.createGetCompletions(doc, stopAutomationRound$) }];

  const flatCoqtopInputs$: Rx.ConnectableObservable<ISertop.ICommand> =
    coqtopInputs$
      // merge sequence of groups of commands into one sequence of commands
      .concatMap(cmds => cmds
      // .do(e => console.log("ELEMENT IN", e))
      // .doOnCompleted(() => console.log("COMPLETED"))
      )
      //  .do(cmd => console.log("ELEMENT OUT", cmd))
      .publish();

  const stmAdd$: Rx.Observable<Command.Control<ControlCommand.StmAdd>> =
    flatCoqtopInputs$
      .filter<Command.Control<any>>(i => i instanceof Command.Control)
      .filter(i => i.controlCommand instanceof ControlCommand.StmAdd);

  const coqtopOutput$s = Sertop.setupCommunication(flatCoqtopInputs$);

  flatCoqtopInputs$.connect();

  const stmAddCounter$ =
    Rx.Observable.merge([
      stmAdd$.map(() => 1),
      stmAdd$
        .concatMap(a =>
          coqtopOutput$s.answer$s.completed$.filter(c => c.cmdTag === a.tag).take(1)
        )
        .map(() => -1),
      // flatCoqtopInputs$
      //   .filter<Command.Control<any>>(i => i instanceof Command.Control)
      //   .filter(i => i.controlCommand instanceof ControlCommand.Quit)
      //   .map(() => 1),
    ])
      .scan((acc, elt) => acc + elt, 0);

  // stmAddCounter$.subscribe(c => console.log("ADD COUNTER", c));

  const stmCancelEditAtCanceledCounter$ =
    Rx.Observable.merge([
      flatCoqtopInputs$
        .filter<Command.Control<any>>(i => i instanceof Command.Control)
        .filter(i => i.controlCommand instanceof ControlCommand.StmCancel)
        .map(_ => 1),
      flatCoqtopInputs$
        .filter<Command.Control<any>>(i => i instanceof Command.Control)
        .filter(i => i.controlCommand instanceof ControlCommand.StmEditAt)
        .map(_ => 1),
      coqtopOutput$s.answer$s.stmCanceled$
        .map(_ => -1),
    ])
      .scan((acc, elt) => acc + elt, 0);

  // stmCancelEditAtCanceledCounter$.subscribe(c => console.log("COUNT", c));

  const stmActionsInFlightCounter$: Rx.Observable<number> =
    Rx.Observable.combineLatest(
      stmAddCounter$,
      stmCancelEditAtCanceledCounter$,
      (x, y) => x + y
    );

  // stmActionsInFlightCounter$.subscribe(c => console.log("COUNT", c));

  /*
  Feedback comes back untagged, so need the zip to keep track of the relationship
  between input PeaCoqGetContext and the output context...
  */
  Rx.Observable.zip(
    peaCoqGetContext$,
    coqtopOutput$s.feedback$s.message$s.notice$.filter(m => m.routeId === peaCoqGetContextRouteId)
  ).subscribe(([cmd, fbk]) => {
    // console.log(cmd, fbk);
    const stateId = cmd.controlCommand.queryOptions.sid;
    const rawContext = fbk.feedbackContent.message;
    const sentence = doc.getSentenceByStateId(stateId);

    sentence.caseOf<void>({
      nothing: () => { },
      just: sentence => {

        if (!(sentence.stage instanceof Stage.Processed)) { debugger; }
        const stage: IProcessed = <any>sentence.stage;

        if (DebugFlags.rawPeaCoqContext) { console.log(rawContext); }
        if (rawContext.length === 0) {
          stage.setContext(emptyContext);
        } else {
          const context = Context.create(rawContext);
          stage.setContext(context);
        }

      }
    })
  });

  ProofTreeAutomation.setup({
    stmActionsInFlightCounter$,
    completed$: coqtopOutput$s.answer$s.completed$,
    doc,
    error$: coqtopOutput$s.feedback$s.message$s.error$,
    notice$: coqtopOutput$s.feedback$s.message$s.notice$,
    queryForTacticToTry$,
    stmAdded$: coqtopOutput$s.answer$s.stmAdded$,
    stopAutomationRound$,
    debouncedTip$: doc.debouncedTip$,
    tip$: doc.tip$,
  });

  coqtopOutput$s.answer$s.stmAdded$.subscribe(a => {
    // console.log("STM ADDED", a);
    const allEdits = doc.getSentencesToProcess();
    const edit = _(allEdits).find(e => isJust(e.commandTag) && fromJust(e.commandTag) === a.cmdTag);
    if (!edit) { return; } // this happens for a number of reasons...
    const newStage = new Stage.BeingProcessed(edit.stage, a.answer.stateId);
    edit.setStage(newStage);
  });

  const nextBecauseGoTo$ = setupUserInteractionForwardGoto(
    doc,
    forwardGoTo$.map(goto => goto.destinationPos),
    coqtopOutput$s.feedback$s.message$s.error$
  );

  nextBecauseGoTo$
    .delay(0) // this is needed to set up the feedback loop properly
    .subscribe(() => nextSubject.onNext({}));

  coqtopOutput$s.feedback$s.processed$
    .subscribe(f => {
      // console.log("PROCESSED", f);
      switch (f.editOrState) {
        case EditOrState.State:
          const stateId = f.editOrStateId;
          const editsBeingProcessed = doc.getSentencesBeingProcessed();
          const edit = _(editsBeingProcessed).find(e => e.stage.stateId === stateId);
          if (edit) {
            const newStage = new Stage.Processed(edit.stage, peaCoqGetContext$);
            edit.setStage(newStage);
            // if (
            //   Global.coqDocument.getEditsToProcess().length === 0
            //   && Global.coqDocument.getEditsBeingProcessed().length === 0
            // ) {
            //   Global.coqDocument.moveCursorToPositionAndCenter(edit.stopPosition);
            // }
          } else {
            // this can happen for two reasons:
            // - when reloading
            // - when some sentence fails, we sometimes get processed messages for later sentences
            // debugger;
          }
          break;
        default:
          debugger; // not sure this ever happens
      }
    });

  const stmCanceledFiltered$ = new Rx.Subject<ISertop.IAnswer<ISertop.IStmCanceled>>();

  coqtopOutput$s.answer$s.stmCanceled$.subscribe(a => {

    const removedStateIds = a.answer.stateIds;

    // if this looks like a cancel caused by PeaCoq trying tactics, ignore it
    if (!_.some(removedStateIds, sid => isJust(doc.getSentenceByStateId(sid)))) {
      return;
    }

    stmCanceledFiltered$.onNext(a);

    doc.removeSentencesByStateIds(removedStateIds);
    const tip = _.maxBy(doc.getAllSentences(), s => s.sentenceId);
    if (tip) { doc.setTip(tip); }

  });

  // NOTE: CoqExn is pretty useless in indicating which command failed
  // Feedback.ErrorMsg gives the failed state ID
  // NOTE2: Except when the command fails wihtout a state ID! For instance
  // if you "Require Import Nonsense." So need both?
  coqtopOutput$s.feedback$s.message$s.error$.subscribe(e => {
    switch (e.editOrState) {
      case EditOrState.Edit: return;
      case EditOrState.State:
        const cancel = new Command.Control(new ControlCommand.StmCancel([e.editOrStateId]));
        cancelBecauseErrorMsg$.onNext(Rx.Observable.just(cancel));
        break;
      default: debugger;
    }
  });

  // keep this above the subscription that removes edits
  UnderlineError.setup(
    doc,
    coqtopOutput$s.feedback$s.message$s.error$,
    Rx.Observable.merge([
      inputsThatChangeErrorState$
    ])
  );

  // keep this above the subscription that removes edits
  new CoqtopPanel(
    $(w2ui[rightLayoutName].get("bottom").content),
    Rx.Observable.merge(

      coqtopOutput$s.feedback$s.message$s.error$
        .filter(e => e.editOrState === EditOrState.State)
        // due to sending sentences fast, we receive errors for states beyond
        // another failed state. reporting those looks spurious to the user.
        .filter(e => isJust(doc.getSentenceByStateId(e.editOrStateId)))
        .map(e => ({
          message: e.feedbackContent.message,
          level: PeaCoqMessageLevel.Danger,
        })),

      coqtopOutput$s.feedback$s.message$s.error$
        .filter(e => e.editOrState === EditOrState.Edit)
        .map(e => ({
          message: e.feedbackContent.message,
          level: PeaCoqMessageLevel.Danger,
        })),

      coqtopOutput$s.feedback$s.message$s.notice$
        .filter(e => e.routeId === 0) // other routes are used by PeaCoq
        .map(e => ({
          message: e.feedbackContent.message,
          level: PeaCoqMessageLevel.Success,
        }))

    ),
    userActionStreams.loadedFile$
  );

  // This used to be simply:
  // - subscribe to coqExn$
  // - remove sentences whose cmdTag >= exn.cmdTag
  // But this won't work with automation, because sometimes a sentence
  // is created in the middle of an automation round, and some
  // automation sentences will have a low cmdTag and raise a CoqExn.
  // We must track provenance of the CoqExn and only remove sentences
  // when it happened because of user action.

  const stmQuery$ =
    flatCoqtopInputs$
      .filter<Command.Control<any>>(i => i instanceof Command.Control)
      .filter(i => i.controlCommand instanceof ControlCommand.StmQuery);

  // keep this under subscribers who need the edit to exist
  Rx.Observable.merge(
    // Assuming `CoqExn`s occur after `StmAdd` and `StmQuery` only.
    stmAdd$
      .filter(a => !a.controlCommand.fromAutomation)
      .flatMap(a =>
        coqtopOutput$s.answer$s.coqExn$.filter(e => e.cmdTag === a.tag)
          .take(1).takeUntil(coqtopOutput$s.answer$s.completed$.filter(c => c.cmdTag === a.tag))
      ),
    stmQuery$
      .filter(a => !a.controlCommand.fromAutomation)
      .flatMap(a =>
        coqtopOutput$s.answer$s.coqExn$.filter(e => e.cmdTag === a.tag)
          .take(1).takeUntil(coqtopOutput$s.answer$s.completed$.filter(c => c.cmdTag === a.tag))
      ),
  ).subscribe(e => {
    // debugger;
    doc.removeSentences(s => s.commandTag.caseOf({
      nothing: () => false,
      just: t => +t >= +e.cmdTag,
    }));
  });

  // keep this under subscribers who need the edit to exist
  coqtopOutput$s.feedback$s.message$s.error$.subscribe(e => {
    switch (e.editOrState) {
      case EditOrState.Edit: return;
      case EditOrState.State:
        const failedStateId = e.editOrStateId;
        const failedSentence = doc.getSentenceByStateId(failedStateId);
        failedSentence.caseOf({
          nothing: () => {
            // This happens when commands fail before producing a state
          },
          just: s => doc.removeSentences(e => e.sentenceId >= s.sentenceId),
        });
        break;
      default: debugger;
    }
  });

  // const editorError$: Rx.Observable<IEditorError> =
  //   coqtopOutput$s.valueFail$
  //     .map(vf => pimpMyError(vf))
  //     .share();
  //
  // editorError$.subscribe(ee =>
  //   Global.coqDocument.removeEditAndFollowingOnes(ee.failedEdit)
  // );
  //
  // new CoqtopPanel(
  //   $(w2ui[rightLayoutName].get("bottom").content),
  //   coqtopOutput$s.feedback$s.errorMsg$,
  //   coqtopOutput$s.message$
  // );

  // editorError$.subscribe(ee => ee.range.fmap(range =>
  //   Global.coqDocument.markError(range)
  // ));

  // editorError$.subscribe(ee =>
  //   // so, apparently we won't receive feedbacks for the edits before this one
  //   // so we need to mark them all processed...
  //   _(Global.coqDocument.getEditsBeingProcessed())
  //     // ASSUMPTION: state IDs are assigned monotonically
  //     .filter(e => e.stage.stateId < ee.error.stateId)
  //     .each(_ => { debugger; })
  //     .each(e => e.setStage(new Edit.Processed(e.stage, queriesObserver)))
  // );

  // setupTextCursorPositionUpdate(
  //   Global.coqDocument.edits.editProcessed$,
  //   editorError$,
  //   previousEditToReach$,
  //   editsToProcessStream
  // );

  // coqtopOutput$s.valueGood$s.editAt$
  //   .subscribe(r => {
  //     const processedEdits = Global.coqDocument.getProcessedEdits();
  //     const firstEditAfter =
  //       _(processedEdits).find(e => e.stage.stateId > (<CoqtopInput.EditAt>r.input).stateId);
  //     if (firstEditAfter) {
  //       Global.coqDocument.removeEditAndFollowingOnes(firstEditAfter);
  //     }
  //   });

  // I'm not sure when this happens, for now I'll assume it doesn't
  // coqtopOutput$s.valueGood$s.editAt$
  //   .subscribe(io => {
  //     if (io.output.response.contents.hasOwnProperty("Right")) { throw io; }
  //   });

  // Rx.Observable.empty() // stmCanceled
  //   .subscribe(r => onStmCanceled(
  //     hideProofTreePanel,
  //     r.input.getArgs()
  //   ));

  ProofTreeSetup.setup({
    doc,
    hideProofTreePanel,
    loadedFile$: userActionStreams.loadedFile$,
    resize$,
    sentenceProcessed$: doc.sentenceProcessed$,
    showProofTreePanel,
    stmCanceled$: stmCanceledFiltered$,
  });

});

function updateCoqtopTabs(context: PeaCoqContext) {
  console.log("TODO: updateCoqtopTabs");
  // clearCoqtopTabs(false);
  // if (context.length > 0) {
  //   pretty.div.append(context[0].getHTML());
  //   foreground.setValue(goals.fgGoals[0].toString(), false);
  // }
}

export function onResize(doc: ICoqDocument): void {
  doc.editor.resize();
  doc.getActiveProofTree().fmap(t => {
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

function updateFontSize(doc: ICoqDocument): void {
  doc.editor.setOption("fontSize", fontSize);
  doc.contextPanel.onFontSizeChanged(fontSize);
  jss.set("#pretty-content", { "font-size": fontSize + "px" });
  jss.set("svg body", { "font-size": fontSize + "px" });
  doc.getActiveProofTree().fmap(t => t.update());
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
  doc: ICoqDocument,
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
    .subscribe(() => { updateFontSize(doc); });
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
    .subscribe(({}) => saveFile(doc));
  const loadedFilesStream = setupLoadFile(doc);
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
