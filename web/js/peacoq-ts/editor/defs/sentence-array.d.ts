interface ISentenceArray {
  sentenceChangedStage$: Rx.Observable<ISentence<IStage>>;
  sentenceBeingProcessed$: Rx.Observable<ISentence<IBeingProcessed>>;
  sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>;
  sentenceCreated$: Rx.Observable<ISentence<IStage>>;
  sentenceRemoved$: Rx.Observable<ISentence<IStage>>;
  createSentence(
    document: ICoqDocument,
    startPosition: AceAjax.Position,
    stopPosition: AceAjax.Position,
    query: string,
    previousSentence: Maybe<ISentence<any>>,
    stage: IToProcess
  ): ISentence<IToProcess>;
  getAll(): ISentence<any>[];
  getLast(): Maybe<ISentence<any>>;
  remove(r: ISentence<any>): void;
  removeAll(): void;
  // removeEditAndFollowingOnes(e: ISentence<any>): void;
  removeSentences(pred: (e: ISentence<any>) => boolean): void;
  // removeFollowingEdits(e: ISentence<any>): void;
  // replace(id: number, e: IEdit<any>): void;
}
