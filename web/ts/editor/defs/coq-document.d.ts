type Tip = Maybe<ISentence<IStage>>

interface ICoqDocument {
  addsToProcess$: Rx.Observable<StmAdd$>
  command$: Rx.Observable<Command$>
  contextPanel: IContextPanel
  // editor: AceAjax.Editor
  editor: IEditor
  // editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>
  sentences: ISentenceArray
  // endAnchor: AceAjax.Anchor
  proofTrees: IProofTreeStack
  sentencesChanged$: Rx.Observable<{}>
  sentenceBeingProcessed$: Rx.Observable<ISentence<IBeingProcessed>>
  sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>
  // session: AceAjax.IEditSession
  debouncedTip$: Rx.Observable<Tip>
  tip$: Rx.Observable<Tip>
  input$: Command$
  output$s: CoqtopOutputStreams

  getActiveProofTree(): Maybe<IProofTree>
  getAllSentences(): ISentence<IStage>[]
  getPositionEnd(): IPosition
  getTextRange(range: IEditorRange): string
  getSentenceByStateId(s: StateId): Maybe<ISentence<IStage>>
  getSentenceByTag(tag: CommandTag): Maybe<ISentence<IStage>>
  getSentenceAtPosition(pos: IPosition): Maybe<ISentence<IStage>>
  getSentencesBeingProcessed(): ISentence<IBeingProcessed>[]
  getSentencesToProcess(): ISentence<IToProcess>[]
  getProcessedSentences(): ISentence<IProcessed>[]
  // getLastSentence(): Maybe<ISentence<IEditStage>>
  getLastSentenceStop(): IPosition
  markError(range: IEditorRange, clear$: Rx.Observable<{}>): void
  moveCursorToPositionAndCenter(pos: IPosition): void
  movePositionRight(pos: IPosition, n: number): IPosition
  next(): void
  // nextSentence(next$: Rx.Observable<{}>): Rx.Observable<ISentence<IToProcess>>
  removeAllSentences(): void
  removeSentence(e: ISentence<IStage>): void
  // removeEditAndFollowingOnes(e: ISentence<IEditStage>): void
  removeSentences(pred: (e: ISentence<IStage>) => boolean): void
  removeSentencesByStateIds(ids: StateId[]): void
  // removeFollowingEdits(e: ISentence<IEditStage>): void
  resetEditor(s: string): void
  sendCommands(s: Command$): void
  setTip(tip: Tip): void
}
