interface ISentence<S extends IStage> {
    array: ISentenceArray
    commandTag: Maybe<CommandTag>
    completionAdded$: Rx.Subject<{}> // should be:
    // completionAdded$: Rx.Observable<{}>
    // but TypeScript compiler is super slow with that (see https://github.com/Microsoft/TypeScript/issues/9791 for information)
    completions: { [group: string]: { [tactic: string]: PeaCoqContext } }
    previousSentence: Maybe<ISentence<any>>
    query: string
    sentenceId: number
    stage: S
    stage$: Rx.Observable<IStage>
    startPosition: AceAjax.Position
    stopPosition: AceAjax.Position

    addCompletion(tactic: string, group: string, context: PeaCoqContext): void
    cleanup(): void
    containsPosition(p: AceAjax.Position): boolean
    getColor(): string
    getPreviousStateId(): Maybe<number>
    getBeingProcessed$(): Rx.Observable<IBeingProcessed>
    // getProcessedStage(): Promise<IProcessed>
    getProcessed$(): Rx.Observable<IProcessed>
    getStateId(): Maybe<number>
    highlight(): void
    setStage<T extends IStage>(stage: T): ISentence<T>
    unhighlight(): void
    waitUntilProcessed(): Rx.Observable<ISentence<IProcessed>>
}
