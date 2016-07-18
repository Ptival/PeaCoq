interface IEditor {

}

interface IContextPanel {
  clear(): void;
  display(c: PeaCoqContext): void;
  onFontSizeChanged(size: number): void;
  onResize(): void;
  setTheme(theme: string): void;
}

interface ITabs {
  pretty: ITab;
  foreground: IEditorTab;
  background: IEditorTab;
  shelved: IEditorTab;
  givenUp: IEditorTab;
}

/* TODO: maybe fuse the parts of the toolbar and shortcuts that overlap? */

interface ToolbarStreams {
  fontDecrease: Rx.Observable<{}>;
  fontIncrease: Rx.Observable<{}>;
  goToCaret: Rx.Observable<{}>;
  load: Rx.Observable<{}>;
  next: Rx.Observable<{}>;
  previous: Rx.Observable<{}>;
  save: Rx.Observable<{}>;
}

interface ShortcutsStreams {
  fontIncrease: Rx.Observable<{}>;
  fontDecrease: Rx.Observable<{}>;
  goToCaret: Rx.Observable<{}>;
  load: Rx.Observable<{}>;
  next: Rx.Observable<{}>;
  previous: Rx.Observable<{}>;
  save: Rx.Observable<{}>;
}

interface ISentenceArray {
  sentenceChangedStage$: Rx.Observable<ISentence<IStage>>;
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

interface ICoqDocument {
  contextPanel: IContextPanel;
  editor: AceAjax.Editor;
  editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>;
  sentences: ISentenceArray;
  endAnchor: AceAjax.Anchor;
  proofTrees: IProofTree[];
  sentencesChanged$: Rx.Observable<{}>;
  sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>;
  session: AceAjax.IEditSession;
  getAllSentences(): ISentence<IStage>[];
  getSentenceByStateId(s: StateId): Maybe<ISentence<IStage>>;
  getSentenceByTag(tag: CommandTag): Maybe<ISentence<IStage>>;
  getSentenceAtPosition(pos: AceAjax.Position): Maybe<ISentence<IStage>>;
  getSentencesBeingProcessed(): ISentence<IBeingProcessed>[];
  getSentencesToProcess(): ISentence<IToProcess>[];
  getProcessedSentences(): ISentence<IProcessed>[];
  // getLastSentence(): Maybe<ISentence<IEditStage>>;
  getLastSentenceStop(): AceAjax.Position;
  markError(range: AceAjax.Range, clear$: Rx.Observable<{}>): void;
  moveCursorToPositionAndCenter(pos: AceAjax.Position): void;
  movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position;
  nextSentence(next$: Rx.Observable<{}>): Rx.Observable<ISentence<IToProcess>>;
  removeAllSentences(): void;
  removeSentence(e: ISentence<IStage>): void;
  // removeEditAndFollowingOnes(e: ISentence<IEditStage>): void;
  removeSentences(pred: (e: ISentence<IStage>) => boolean): void;
  removeSentencesByStateIds(ids: StateId[]): void;
  // removeFollowingEdits(e: ISentence<IEditStage>): void;
  resetEditor(s: string): void;
}

interface ISentence<S extends IStage> {
  array: ISentenceArray;
  commandTag: Maybe<CommandTag>;
  completionAdded$: Rx.Subject<{}>; // should be:
  // completionAdded$: Rx.Observable<{}>;
  // but TypeScript compiler is super slow with that (see https://github.com/Microsoft/TypeScript/issues/9791 for information)
  completions: { [group: string]: { [tactic: string]: PeaCoqContext } };
  previousEdit: Maybe<ISentence<any>>;
  query: string;
  sentenceId: number;
  stage: S;
  stage$: Rx.Observable<IStage>;
  startPosition: AceAjax.Position;
  stopPosition: AceAjax.Position;
  addCompletion(tactic: string, group: string, context: PeaCoqContext): void
  cleanup(): void;
  containsPosition(p: AceAjax.Position): boolean;
  getColor(): string;
  getPreviousStateId(): Maybe<number>;
  getBeingProcessed$(): Rx.Observable<IBeingProcessed>;
  getProcessedStage(): Promise<IProcessed>;
  getStateId(): Maybe<number>;
  highlight(): void;
  setStage<T extends IStage>(stage: T): ISentence<T>;
  unhighlight(): void;
}

interface IStage {
  marker: IEditMarker;
  getColor(): string;
  getStateId(): Maybe<number>;
}

interface IToProcess extends IStage {
  nextStageMarker(): IEditMarker;
}

interface WithStateId {
  stateId: number;
}

interface IBeingProcessed extends IStage, WithStateId {
  nextStageMarker(): IEditMarker;
}

interface IProcessed extends IStage, WithStateId {
  // context: PeaCoqContext | null;
  // editId: number;
  // goals: Maybe<IGoals>;
  //status: IStatus;
  getContext(): Promise<PeaCoqContext>;
  setContext(c: PeaCoqContext): void;
}

interface IEditMarker {
  startPosition: AceAjax.Position;
  stopPosition: AceAjax.Position;
  highlight(): void;
  markBeingProcessed(): void;
  markProcessed(): void;
  remove(): void;
  unhighlight(): void;
}

interface ITab {
  div: JQuery;
  click(): void;
  setCaptionSuffix(s: string): void;
}

interface IEditorTab extends ITab {
  clearValue(): void;
  getValue(): string;
  resize(): void;
  setFontSize(size: number): void;
  setTheme(s: string): void;
  setValue(s: string, switchToTab: boolean);
}

interface IEditorError {
  error: IValueFail;
  failedEdit: ISentence<IBeingProcessed>;
  // lastValidStateId: number,
  // message: string;
  range: Maybe<AceAjax.Range>;
}
