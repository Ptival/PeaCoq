type Tip = Maybe<ISentence<IStage>>

interface ICoqDocument {
    addsToProcess$: Rx.Observable<Add$>
    command$: Rx.Observable<Command$>
    contextPanel: IContextPanel
    editor: AceAjax.Editor
    editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>
    sentences: ISentenceArray
    // endAnchor: AceAjax.Anchor
    proofTrees: IProofTreeStack
    sentencesChanged$: Rx.Observable<{}>
    sentenceBeingProcessed$: Rx.Observable<ISentence<IBeingProcessed>>
    sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>
    session: AceAjax.IEditSession
    debouncedTip$: Rx.Observable<Tip>
    tip$: Rx.Observable<Tip>
    input$: Command$
    output$s: CoqtopOutputStreams

    getActiveProofTree(): Maybe<IProofTree>
    getAllSentences(): ISentence<IStage>[]
    getSentenceByStateId(s: import('../../coq/lib/stateid').t): Maybe<ISentence<IStage>>
    getSentenceByTag(tag: string): Maybe<ISentence<IStage>>
    getSentenceAtPosition(pos: AceAjax.Position): Maybe<ISentence<IStage>>
    getSentencesBeingProcessed(): ISentence<IBeingProcessed>[]
    getSentencesToProcess(): ISentence<IToProcess>[]
    getProcessedSentences(): ISentence<IProcessed>[]
    // getLastSentence(): Maybe<ISentence<IEditStage>>
    getLastSentenceStop(): AceAjax.Position
    markError(range: AceAjax.Range, clear$: Rx.Observable<{}>): void
    moveCursorToPositionAndCenter(pos: AceAjax.Position): void
    movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position
    next(): void
    // nextSentence(next$: Rx.Observable<{}>): Rx.Observable<ISentence<IToProcess>>
    removeAllSentences(): void
    removeSentence(e: ISentence<IStage>): void
    // removeEditAndFollowingOnes(e: ISentence<IEditStage>): void
    removeSentences(pred: (e: ISentence<IStage>) => boolean): void
    removeSentencesByStateIds(ids: import('../../coq/lib/stateid').t[]): void
    // removeFollowingEdits(e: ISentence<IEditStage>): void
    resetEditor(s: string): void
    sendCommands(s: Command$): void
    setTip(tip: Tip): void
}
