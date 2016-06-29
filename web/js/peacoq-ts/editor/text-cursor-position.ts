import * as Global from "../global-variables";
import { ValueFail } from "../coq/value-fail";
import { Processed } from "../coq/feedback-content";

/*
  This takes care of updating the position of the text cursor in the following
  situations:
  - when the final edit of a sequence of edits being processed is processed
  - when an error occurs
  - when the user steps back to a previous edit
  - when the user asks for the next edit to be processed

  An issue that arises is that when an error arises, we still receive a
  processed notification for the last edit that succeeded, after we receive
  the error. To ignore this edit and keep the user centered at the error
  location, we skip 1 notification of edits processed.
*/

export function setupTextCursorPositionUpdate(
  doc: ICoqDocument,
  editProcessed$: Rx.Observable<ISentence<IProcessed>>,
  error$: Rx.Observable<IEditorError>,
  previousEditToReach$: Rx.Observable<ISentence<IEditStage>>,
  nextEditToProcess$: Rx.Observable<ISentence<IToProcess>>
): void {

  const lastEditProcessedStopPosition$ =
    editProcessed$
      .filter(f => doc.getSentencesBeingProcessed().length === 0)
      .filter(f => doc.getSentencesToProcess().length === 0)
      .map(e => e.stopPosition);

  const errorLocation$ =
    error$
      .map(ee => ee.range.caseOf<AceAjax.Position>({
        nothing: () => ee.failedEdit.stopPosition,
        just: r => r.start,
      }));

  const inhibitLastEditAfterError$ =
    Rx.Observable
      .merge([
        lastEditProcessedStopPosition$.map(() => false),
        errorLocation$.map(() => true),
      ])
      .distinctUntilChanged(); // might as well

  const previousEditStopPosition$ =
    previousEditToReach$
      .map(e => e.stopPosition);

  const nextEditStopPosition$ =
    nextEditToProcess$
      .map(e => e.stopPosition);

  const positionUpdate$ = Rx.Observable.merge([
    lastEditProcessedStopPosition$.pausable(inhibitLastEditAfterError$),
    errorLocation$,
    previousEditStopPosition$,
    nextEditStopPosition$
  ]);

  positionUpdate$.subscribe(pos =>
    doc.moveCursorToPositionAndCenter(pos)
  );

}
