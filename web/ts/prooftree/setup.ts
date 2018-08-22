import { hide as hideProofTreePanel, show as showProofTreePanel } from './panel'
import * as ProofTreeHandlers from './prooftree-handlers'

export function setup(
  doc : ICoqDocument,
  loadedFile$ : Rx.Observable<{}>,
  resize$ : Rx.Observable<{}>,
  stmCanceled$ : Rx.Observable<ISertop.IAnswer<ISertop.IStmCanceled>>,
  bottomLayout : W2UI.W2Layout
) : void {

  resize$.debounce(250).subscribe(() => {
    if (doc.proofTrees.length === 0) { return }
    const activeProofTree = doc.proofTrees.peek()
    activeProofTree.resize(
      $('#prooftree').parent().width()  || 100,
      $('#prooftree').parent().height() || 100
    )
  })

  const exitProofTree$ = new Rx.Subject<{}>()
  function hideProofTreePanelAndSignal() {
    exitProofTree$.onNext({})
    hideProofTreePanel(bottomLayout)
  }

  loadedFile$.subscribe(hideProofTreePanelAndSignal)

  // We want to start a ProofTree session everytime :
  // - the last sentence processed is 'Proof.'
  // - no further sentence remains to be processed
  doc.sentenceProcessed$
    // .do(s => console.log('sentence processed', s))
    .filter(s => CoqStringUtils.coqTrim(s.query) === 'Proof.')
    .filter(s => doc.getSentencesToProcess().length === 0)
    .filter(s => doc.getSentencesBeingProcessed().length === 0)
    // .do(s => console.log('Starting to listen because of sentence', s))
    .flatMap(s =>
      doc.sentenceProcessed$.startWith(s)
        .takeUntil(exitProofTree$)
        // .doOnCompleted(() => console.log('Stopped listening'))
        .flatMap(s => s.stage.getContext().then(c => ({ sentence : s, context : c })))
    )
    .subscribe(({ sentence, context }) => {
      ProofTreeHandlers.proofTreeOnEdit(
        doc, () => showProofTreePanel(bottomLayout), hideProofTreePanelAndSignal,
        sentence.query, sentence.stage.stateId, context
      )
    })

  stmCanceled$.subscribe(c => {
    // console.log('proofTree cancels IDs', c.answer.stateIds)
    ProofTreeHandlers.onStmCanceled(
      doc,
      hideProofTreePanelAndSignal,
      c.answer.stateIds
    )
  })

}
