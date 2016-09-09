export function setup(
  doc: ICoqDocument,
  stmCancel$: StmCancel$,
  stmCanceled$: StmCanceled$
): StmCanceled$ {
  const stmCanceledFiltered$ = new Rx.Subject<ISertop.IAnswer<ISertop.IStmCanceled>>();

  // Now that we pre-emptively removed sentences from the view before they are
  // acknowledged by the backend, checking which StmCanceled were caused by
  // PeaCoq's automation is more complex than checking if the removed stateIds
  // match a sentence in the document.
  stmCancel$
    // .filter(c => !c.controlCommand.fromAutomation)
    .flatMap(c => stmCanceled$.filter(e => e.cmdTag === c.tag))
    .subscribe(a => {
      const removedStateIds = a.answer.stateIds;
      stmCanceledFiltered$.onNext(a);
      doc.removeSentencesByStateIds(removedStateIds);
      const tip = _.maxBy(doc.getAllSentences(), s => s.sentenceId);
      doc.setTip(tip ? just(tip) : nothing());
    });

  return stmCanceledFiltered$;
}
