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
  editChangedStage$: Rx.Observable<ISentence<IEditStage>>;
  editProcessed$: Rx.Observable<ISentence<IProcessed>>;
  editCreated$: Rx.Observable<ISentence<IEditStage>>;
  editRemoved$: Rx.Observable<ISentence<IEditStage>>;
  createEdit(
    document: ICoqDocument,
    startPosition: AceAjax.Position,
    stopPosition: AceAjax.Position,
    query: string,
    previousEdit: Maybe<ISentence<any>>,
    stage: IToProcess
  ): ISentence<IToProcess>;
  getAll(): ISentence<any>[];
  getLast(): Maybe<ISentence<any>>;
  remove(r: ISentence<any>): void;
  removeAll(): void;
  // removeEditAndFollowingOnes(e: ISentence<any>): void;
  removeEdits(pred: (e: ISentence<any>) => boolean): void;
  // removeFollowingEdits(e: ISentence<any>): void;
  // replace(id: number, e: IEdit<any>): void;
}

interface ICoqDocument {
  contextPanel: IContextPanel;
  editor: AceAjax.Editor;
  editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>;
  edits: ISentenceArray;
  endAnchor: AceAjax.Anchor;
  sentencesChanged$: Rx.Observable<{}>;
  session: AceAjax.IEditSession;
  getAllSentences(): ISentence<any>[];
  getSentenceAtStateId(s: StateId): Maybe<ISentence<any>>;
  getSentenceAtPosition(pos: AceAjax.Position): Maybe<ISentence<any>>;
  getSentencesBeingProcessed(): ISentence<IBeingProcessed>[];
  getSentencesToProcess(): ISentence<IToProcess>[];
  getProcessedSentences(): ISentence<IProcessed>[];
  // getLastSentence(): Maybe<ISentence<IEditStage>>;
  getLastSentenceStop(): AceAjax.Position;
  markError(range: AceAjax.Range, clear$: Rx.Observable<{}>): void;
  moveCursorToPositionAndCenter(pos: AceAjax.Position): void;
  movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position;
  nextSentence(next$: Rx.Observable<{}>): Rx.Observable<ISentence<IToProcess>>;
  removeAllEdits(): void;
  removeEdit(e: ISentence<IEditStage>): void;
  // removeEditAndFollowingOnes(e: ISentence<IEditStage>): void;
  removeEdits(pred: (e: ISentence<IEditStage>) => boolean): void;
  removeEditsByStateIds(ids: StateId[]): void;
  // removeFollowingEdits(e: ISentence<IEditStage>): void;
  resetEditor(s: string): void;
}

interface ISentence<S extends IEditStage> {
  array: ISentenceArray;
  commandTag: Maybe<number>;
  previousEdit: Maybe<ISentence<any>>;
  query: string;
  sentenceId: number;
  stage: S;
  stage$: Rx.Observable<IEditStage>;
  startPosition: AceAjax.Position;
  stopPosition: AceAjax.Position;
  cleanup(): void;
  containsPosition(p: AceAjax.Position): boolean;
  getColor(): string;
  getPreviousStateId(): Maybe<number>;
  getBeingProcessed$(): Rx.Observable<IBeingProcessed>;
  getProcessedStage(): Promise<IProcessed>;
  getStateId(): Maybe<number>;
  highlight(): void;
  setStage<T extends IEditStage>(stage: T): ISentence<T>;
  unhighlight(): void;
}

interface IEditStage {
  marker: IEditMarker;
  getColor(): string;
  getStateId(): Maybe<number>;
}

interface IToProcess extends IEditStage {
  nextStageMarker(): IEditMarker;
}

interface WithStateId {
  stateId: number;
}

interface IBeingProcessed extends IEditStage, WithStateId {
  nextStageMarker(): IEditMarker;
}

interface IProcessed extends IEditStage, WithStateId {
  context: PeaCoqContext | null;
  // editId: number;
  // goals: Maybe<IGoals>;
  //status: IStatus;
  // getContext(): Promise<PeaCoqContext>;
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
