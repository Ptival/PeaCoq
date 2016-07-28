import * as ProofTreeHandlers from "./prooftree-handlers";

interface ProofTreeSetupInput {
  doc: ICoqDocument;
  hideProofTreePanel: () => void;
  resize$: Rx.Observable<{}>;
  sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>;
  showProofTreePanel: () => Promise<{}>;
  stmCanceled$: Rx.Observable<ISertop.IAnswer<ISertop.IStmCanceled>>;
}

export function setup(i: ProofTreeSetupInput): void {
  const {
    doc,
    hideProofTreePanel,
    resize$,
    sentenceProcessed$,
    showProofTreePanel,
    stmCanceled$,
  } = i;

  resize$.debounce(250).subscribe(() => {
    if (doc.proofTrees.length === 0) { return; }
    const activeProofTree = doc.proofTrees[0];
    activeProofTree.resize(
      $("#prooftree").parent().width(),
      $("#prooftree").parent().height()
    );
  });

  sentenceProcessed$
    .flatMap(s => s.stage.getContext().then(c => ({ sentence: s, context: c })))
    .subscribe(({ sentence, context }) => {
      // console.log("proofTree sees sentence", sentence);
      ProofTreeHandlers.proofTreeOnEdit(
        doc, showProofTreePanel, hideProofTreePanel,
        sentence.query, sentence.stage.stateId, context
      )
    });

  stmCanceled$.subscribe(c => {
    // console.log("proofTree cancels IDs", c.answer.stateIds);
    ProofTreeHandlers.onStmCanceled(
      doc,
      hideProofTreePanel,
      c.answer.stateIds
    )
  });

}
