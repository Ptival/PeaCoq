export function setup(
  doc : ICoqDocument,
  coqExn$ : CoqExn$,
  stmAdd$ : StmAdd$,
  stmQuery$ : StmQuery$,
  completed$ : Completed$
) : void {
  // This used to be simply :
  // - subscribe to coqExn$
  // - remove sentences whose cmdTag >= exn.cmdTag
  // But this won't work with automation, because sometimes a sentence
  // is created in the middle of an automation round, and some
  // automation sentences will have a low cmdTag and raise a CoqExn.
  // We must track provenance of the CoqExn and only remove sentences
  // when it happened because of user action.
  Rx.Observable.merge(
    // Assuming `CoqExn`s occur after `StmAdd` and `StmQuery` only.
    stmAdd$
      .filter(a => !a.controlCommand.fromAutomation)
      .flatMap(a =>
        coqExn$.filter(e => e.cmdTag === a.tag)
          .take(1).takeUntil(completed$.filter(c => c.cmdTag === a.tag))
      ),
    stmQuery$
      .filter(a => !a.controlCommand.fromAutomation)
      .flatMap(a =>
        coqExn$.filter(e => e.cmdTag === a.tag)
          .take(1).takeUntil(completed$.filter(c => c.cmdTag === a.tag))
      )
  ).subscribe(e => {
    // debugger
    doc.removeSentences(s => s.commandTag.caseOf({
      nothing : () => false,
      just : t => +t >= +e.cmdTag,
    }))
  })
}
