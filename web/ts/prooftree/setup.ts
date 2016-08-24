import * as ProofTreeHandlers from "./prooftree-handlers";

interface ProofTreeSetupInput {
  doc: ICoqDocument;
  hideProofTreePanel: () => void;
  loadedFile$: Rx.Observable<{}>;
  resize$: Rx.Observable<{}>;
  sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>;
  showProofTreePanel: () => Promise<{}>;
  stmCanceled$: Rx.Observable<ISertop.IAnswer<ISertop.IStmCanceled>>;
}

export function setup(i: ProofTreeSetupInput): void {
  const {
    doc,
    hideProofTreePanel,
    loadedFile$,
    resize$,
    sentenceProcessed$,
    showProofTreePanel,
    stmCanceled$,
  } = i;

  resize$.debounce(250).subscribe(() => {
    if (doc.proofTrees.length === 0) { return; }
    const activeProofTree = doc.proofTrees.peek();
    activeProofTree.resize(
      $("#prooftree").parent().width(),
      $("#prooftree").parent().height()
    );
  });

  const exitProofTree$ = new Rx.Subject<{}>();
  function hideProofTreePanelAndSignal() {
    exitProofTree$.onNext({});
    hideProofTreePanel();
  }

  loadedFile$.subscribe(hideProofTreePanelAndSignal);

  // We want to start a ProofTree session everytime:
  // - the last sentence processed is "Proof."
  // - no further sentence remains to be processed
  sentenceProcessed$
    .filter(s => CoqStringUtils.coqTrim(s.query) === "Proof.")
    .filter(s => doc.getSentencesToProcess().length === 0)
    .filter(s => doc.getSentencesBeingProcessed().length === 0)
    // .do(s => console.log("Starting to listen because of sentence", s))
    .flatMap(s =>
      sentenceProcessed$.startWith(s)
        .takeUntil(exitProofTree$)
        // .doOnCompleted(() => console.log("Stopped listening"))
        .flatMap(s => s.stage.getContext().then(c => ({ sentence: s, context: c })))
    )
    .subscribe(({ sentence, context }) => {
      ProofTreeHandlers.proofTreeOnEdit(
        doc, showProofTreePanel, hideProofTreePanelAndSignal,
        sentence.query, sentence.stage.stateId, context
      );
    });

  stmCanceled$.subscribe(c => {
    // console.log("proofTree cancels IDs", c.answer.stateIds);
    ProofTreeHandlers.onStmCanceled(
      doc,
      hideProofTreePanelAndSignal,
      c.answer.stateIds
    )
  });

}
