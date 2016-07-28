import * as ProofTreeHandlers from "./prooftree-handlers";

interface ProofTreeSetupInput {
  doc: ICoqDocument;
  hideProofTreePanel: () => void;
  sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>;
  showProofTreePanel: () => Promise<{}>;
  stmCanceled$: Rx.Observable<ISertop.IAnswer<ISertop.IStmCanceled>>;
}

interface ProofTreeSetupOutput {
}

export function setup(i: ProofTreeSetupInput): ProofTreeSetupOutput {
  const {
    doc,
    hideProofTreePanel,
    sentenceProcessed$,
    showProofTreePanel,
    stmCanceled$,
  } = i;
  const hideProofTreePanel$ = new Rx.Subject();
  const showProofTreePanel$ = new Rx.Subject();

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

  return {
    hideProofTreePanel$,
    showProofTreePanel$,
  };
}
