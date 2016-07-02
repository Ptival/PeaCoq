export function setup(
  doc: ICoqDocument,
  errorMsg$: Rx.Observable<ErrorMessageFeedback>,
  clear$: Rx.Observable<{}>
): void {
  errorMsg$.subscribe(e => {
    switch (e.editOrState) {
      case EditOrState.State:
        const failedEdit = doc.getSentenceAtStateId(e.editOrStateId);
        failedEdit.fmap(failedEdit => {
          e.feedbackContent.location.fmap(location => {
            const errorStartIndex = location.bp;
            const errorStopIndex = location.ep;
            // to compute the document location, we must map the location (nb of characters)
            // to the on-screen position (by virtually moving the cursor right)
            const errorStart = doc.movePositionRight(failedEdit.startPosition, errorStartIndex);
            const errorStop = doc.movePositionRight(failedEdit.startPosition, errorStopIndex);
            const range = new AceAjax.Range(errorStart.row, errorStart.column, errorStop.row, errorStop.column);
            doc.markError(range, clear$);
          });
        });
        break;
      default: debugger;
    }
  });
}

// export function pimpMyError(vf: IValueFail): IEditorError {
//   // Warning: the failed edit is not necessarily the first edit being processed
//   const editsBeingProcessed = Global.coqDocument.getEditsBeingProcessed();
//   const failedEdit = _(editsBeingProcessed)
//     .find(ed => ed.stage.stateId > vf.stateId);
//   const range = vf.location.fmap(loc => {
//     // to compute the document location, we must map the location (nb of characters)
//     // to the on-screen position (by virtually moving the cursor right)
//     const errorStart = Global.coqDocument.movePositionRight(failedEdit.startPosition, loc.startPos);
//     const errorStop = Global.coqDocument.movePositionRight(failedEdit.startPosition, loc.stopPos);
//     return new AceAjax.Range(errorStart.row, errorStart.column, errorStop.row, errorStop.column);
//   });
//   return {
//     error: vf,
//     failedEdit: failedEdit,
//     range: range,
//   }
// }
