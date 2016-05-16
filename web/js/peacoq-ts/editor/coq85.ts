import * as CoqtopInput from "./../coqtop-input";
import * as Global from "./../global-variables";
import * as Edit from "./edit";
// TODO: the thing causing this import should go elsewhere
import { Warning } from "../coq/message-level";

// import { Strictly } from "./strictly";

// let AceAnchor = ace.require("ace/anchor").Anchor;
// let AceRange = ace.require("ace/range").Range;
// let AceRangeList = ace.require("ace/range_list").RangeList;
// let AceSelection = ace.require("ace/selection").Selection;

// let autoLayout = false;

// let maxLength = 2000;
//
// function onFeedback(f: IFeedback) {
//   let current = Global.feedback.getValue().substring(0, maxLength);
//   let now = new Date();
//   Global.feedback.setValue(
//     "[" + now.toString().substring(16, 24) + "] " + f.toString() +
//     "\n" + current,
//     false
//   );
// }

function isQueryWarning(m: IMessage) {
  return (
    m.level.constructor === Warning && m.content.indexOf(
      "Query commands should not be inserted in scripts"
    ) > -1
  );
}

// function onMessage(m: IMessage) {
//   m.display();
// }

function parentHeight(): string {
  return $(this).parent().css("height");
}

function halfParentHeight(): string {
  return (parseInt($(this).parent().css("height"), 10) / 2) + "px";
}

function resetCoqtop(): Promise<any> {
  return Promise.resolve();
  // return peaCoqEditAt(1)
  //   .then(() => peaCoqAddPrime("Require Import PeaCoq.PeaCoq."))
  //   .then(() => peaCoqStatus(false));
}

export function setupSyntaxHovering() {

  $(document)
    .on('mouseenter mouseover', '.syntax', function(e) {
      $(this).toggleClass('peacoq-highlight', true);
      e.stopImmediatePropagation();
    })
    .on('mouseout mouseleave', '.syntax', function(e) {
      $(this).toggleClass('peacoq-highlight', false);
      e.stopImmediatePropagation();
    })
    ;

}

let unlockedAnchor;
let unlockedMarker;

function clearCoqtopTabs(clearFailures: boolean): void {
  let tabsToClear = [
    Global.tabs.foreground,
    Global.tabs.background,
    Global.tabs.shelved,
    Global.tabs.givenUp,
    // Global.tabs.notices,
    // Global.tabs.warnings,
    // Global.tabs.errors,
    // Global.tabs.infos
  ];
  // if (clearFailures) { tabsToClear.push(Global.tabs.failures); }
  _(tabsToClear)
    .each((et: IEditorTab) => {
      et.clearValue();
    });
  Global.tabs.pretty.div.html("");
}

// function reportFailure(f: string) { //, switchTab: boolean) {
//   // Global.tabs.failures.setValue(f, true);
//   //yif (switchTab) { failures.click(); }
// }

// function getPreviousEditContext(e: IEdit): Maybe<PeaCoqContext> {
//   return e.previousEdit.bind((e) => {
//     let stage = e.stage;
//     return stage instanceof EditStage.Processed ? just(stage.context) : nothing();
//   });
// }

export function onNextReactive(
  doc: ICoqDocument,
  next: Rx.Observable<{}>
): Rx.Observable<IEdit<IToProcess>> {
  return next
    .concatMap<IEdit<IToProcess>>(() => {
      let lastEditStopPos = doc.getLastEditStop();
      let endPos = doc.endAnchor.getPosition();
      let unprocessedRange =
        new AceAjax.Range(
          lastEditStopPos.row, lastEditStopPos.column,
          endPos.row, endPos.column
        );
      let unprocessedText = doc.session.getTextRange(unprocessedRange);
      if (CoqStringUtils.coqTrimLeft(unprocessedText) === "") {
        return [];
      }
      let nextIndex = CoqStringUtils.next(unprocessedText);
      let newStopPos = doc.movePositionRight(lastEditStopPos, nextIndex);
      let query = unprocessedText.substring(0, nextIndex);
      let previousEdit = Global.coqDocument.edits.getLast();
      let stage = new Edit.ToProcess(Global.coqDocument, lastEditStopPos, newStopPos);
      let edit: IEdit<IToProcess> =
        doc.edits.createEdit(Global.coqDocument, lastEditStopPos, newStopPos, query, previousEdit, stage);
      return [edit];
    })
    .do(e => {
      doc.moveCursorToPositionAndCenter(e.stopPosition);
    })
    .share()
    ;
}

/*
rejects if the command was rejected (the catch only cleans up, but
throws the error again)
*/
// function onNext(doc: CoqDocument): Promise<void> {
//   //clearCoqtopTabs();
//   let lastEditStopPos = doc.getLastEditStop();
//   let endPos = doc.endAnchor.getPosition();
//   let unprocessedRange =
//     new AceRange(
//       lastEditStopPos.row, lastEditStopPos.column,
//       endPos.row, endPos.column
//     );
//   let unprocessedText = doc.session.getTextRange(unprocessedRange);
//   if (CoqStringUtils.coqTrimLeft(unprocessedText) === "") {
//     return;
//   }
//   let nextIndex = CoqStringUtils.next(unprocessedText);
//   let newStopPos = movePosRight(doc, lastEditStopPos, nextIndex);
//   let query = unprocessedText.substring(0, nextIndex);
//   let e1 = new EditToProcess(coqDocument, lastEditStopPos, newStopPos, query);
//   doc.editsToProcess.push(e1);
//   return doc.processEdits();
// }

// type EditHandler = (q: string, sid: number, ls: Status, s: Status, g: Goals, c: PeaCoqContext) => void;
// let editHandlers: EditHandler[] = [];

// TODO: there is a better way to rewind with the new STM machinery!
// function rewindToPosition(
//   doc: CoqDocument,
//   targetPos: AceAjax.Position
// ): Promise<any> {
//   let lastEditStopPos = doc.getLastEditStop();
//   if (isAfter(Strictly.Yes, targetPos, lastEditStopPos)
//     || coqDocument.editsToProcess.length > 0
//     || isJust(coqDocument.editBeingProcessed)
//   ) {
//     return Promise.resolve();
//   } else {
//     let cursorPosition = coqDocument.editor.selection.getCursor();
//     let editToRewindTo = _(coqDocument.editsProcessed).find(
//       (e: ProcessedEdit) => e.containsPosition(cursorPosition)
//     );
//     return peaCoqEditAt(editToRewindTo.stateId);
//   }
// }

// function forwardToPosition(
//   doc: CoqDocument,
//   targetPos: AceAjax.Position
// ): Promise<void> {
//   let lastEditStopPos = doc.getLastEditStop();
//   if (isAfter(Strictly.Yes, lastEditStopPos, targetPos)) { return Promise.resolve(); }
//
//   // don't move forward if there is only spaces/comments
//   let range = AceAjax.Range.fromPoints(lastEditStopPos, targetPos);
//   let textRange = doc.session.getDocument().getTextRange(range);
//   if (CoqStringUtils.coqTrim(textRange) === "") { return Promise.resolve(); }
//
//   //console.log(lastEditStopPos, targetPos, coqTrim(textRange), textRange);
//
//   //return onNext(doc).then(() => forwardToPosition(doc, targetPos));
//
//   //onNext(doc);
//   return forwardToPosition(doc, targetPos);
// }

/*
TODO: This should add all the necessary edits to be proven immediately
TODO: Currently, this loops forever if a command fails
TODO: Ideally, the cursor would not jump on completion of these edits
*/
// function onGoToCaret(doc: CoqDocument): Promise<void> {
//   // first, check if this is going forward or backward from the end
//   // of the last edit
//   let cursorPos = doc.editor.getCursorPosition();
//   let lastEditStopPos = doc.getLastEditStop();
//   if (isAfter(Strictly.Yes, cursorPos, lastEditStopPos)) {
//     return forwardToPosition(doc, cursorPos);
//   } else if (isAfter(Strictly.Yes, lastEditStopPos, cursorPos)) {
//     return rewindToPosition(doc, cursorPos);
//   } else {
//     // no need to move
//     return;
//   }
// }

// function onPrevious(doc: CoqDocument): Promise<void> {
//   //clearCoqtopTabs();
//   if (isJust(doc.editBeingProcessed) || doc.editsToProcess.length > 0) {
//     return Promise.resolve();
//   }
//   let lastEdit = _.last(doc.editsProcessed);
//   if (!lastEdit) { return Promise.resolve(); }
//   return (
//     lastEdit.previousEdit
//       .caseOf({
//         nothing: () => resetCoqtop(),
//         just: (pe) => {
//           lastStatus = pe.status;
//           return peaCoqEditAt(pe.stateId);
//         },
//       })
//       .then(() => {
//         lastEdit.remove();
//         doc.session.selection.clearSelection();
//         doc.editor.moveCursorToPosition(lastEdit.getStartPosition());
//         doc.editor.scrollToLine(lastEdit.getStartPosition().row, true, true, () => { });
//         doc.editor.focus();
//         // let prevEdit = _.last(doc.edits);
//         // if (prevEdit !== undefined) {
//         //   updateGoals(prevEdit);
//         //   updatePretty(prevEdit);
//         // }
//       })
//       .catch((vf: ValueFail) => {
//         reportFailure(vf.message);
//         // Hopefully, the goals have not changed?
//         /*
//         let s = peaCoqStatus(false);
//         let g = s.then(peaCoqGoal);
//         return (
//           Promise.all<any>([s, g])
//             .then(
//             ([s, g]: [Status, Goals]) => { return updateForeground(s, g); }
//             )
//           );
//         */
//       })
//   );
//
// }

// type AddResult = {
//   response: any;
//   status: IStatus;
//   goals: IGoals;
// };

export function sameBodyAndType(hyp1: HTMLElement, hyp2: HTMLElement): boolean {
  let children1 = $(hyp1).children().slice(1);
  let children2 = $(hyp2).children().slice(1);
  if (children1.length !== children2.length) { return false; }
  for (let i in _.range(children1.length)) {
    if ($(children1[i]).html() !== $(children2[i]).html()) {
      return false;
    }
  }
  return true;
}

// function killEditsAfterPosition(doc: CoqDocument, pos: AceAjax.Position) {
//   // we will need to rewind to the state before the oldest edit we remove
//   let editToRewindTo: Maybe<ProcessedEdit> = nothing();
//   // we remove all the edits that are after the position that was edited
//   doc.removeEdits(
//     (edit: ProcessedEdit) => isAfter(Strictly.Yes, edit.getStopPosition(), pos),
//     (edit: ProcessedEdit) => {
//       edit.previousEdit.caseOf({
//         nothing: () => { },
//         just: (pe) => {
//           editToRewindTo.caseOf({
//             nothing: () => { editToRewindTo = just(pe); },
//             just: (e) => {
//               if (pe.stateId < e.stateId) { editToRewindTo = just(pe); }
//             },
//           });
//         },
//       })
//     }
//   );
//
//   editToRewindTo.caseOf({
//     nothing: () => { },
//     just: (e) => { peaCoqEditAt(e.stateId); }
//   });
//
// }

function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1);
}

/*
I guess I need to know which outputs correspond to which inputs.
There are two ways to go:
- extend CoqtopInput<T> { metadata: T }, but this will force everyone
  to use the same T
- just add the metadata field without mentioning it, and find it in the
  response, unchanged, this might need a type case
*/

export function processEditsReactive(
  edit: Rx.Observable<IEdit<IToProcess>>
): Rx.Observable<ICoqtopInput> {
  return edit
    // need `concatMap` here to guarantee the commands are processed in
    // the correct order: add, goal, context, add, goal, context, add, ...
    .map(e => {
      let add = new CoqtopInput.AddPrime(e.query);
      add.callback = r => {
        const stateId = r.contents[0];
        const newStage = new Edit.BeingProcessed(e.stage, stateId);
        e.setStage(newStage);
      };
      return add;
    })
    .share();
}
