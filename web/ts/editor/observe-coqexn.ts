export function setup(
  doc: ICoqDocument,
  coqExn$: CoqExn$,
  stmAdd$: StmAdd$,
  stmQuery$: StmQuery$,
  completed$: Completed$
): void {
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
    // debugger;
    doc.removeSentences(s => s.commandTag.caseOf({
      nothing: () => false,
      just: t => +t >= +e.cmdTag,
    }));
  });
}
