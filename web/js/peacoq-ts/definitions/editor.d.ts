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

interface IEditArray {
  editChangedStage$: Rx.Observable<IEdit<IEditStage>>;
  editProcessed$: Rx.Observable<IEdit<IProcessed>>;
  editCreated$: Rx.Observable<IEdit<IEditStage>>;
  editRemoved$: Rx.Observable<IEdit<IEditStage>>;
  createEdit(
    document: ICoqDocument,
    startPosition: AceAjax.Position,
    stopPosition: AceAjax.Position,
    query: string,
    previousEdit: Maybe<IEdit<any>>,
    stage: IToProcess
  ): IEdit<IToProcess>;
  getAll(): IEdit<any>[];
  getLast(): Maybe<IEdit<any>>;
  remove(r: IEdit<any>): void;
  removeAll(): void;
  removeEditAndFollowingOnes(e: IEdit<any>): void;
  removeFollowingEdits(e: IEdit<any>): void;
  // replace(id: number, e: IEdit<any>): void;
}

interface ICoqDocument {
  editor: AceAjax.Editor;
  editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>;
  edits: IEditArray;
  endAnchor: AceAjax.Anchor;
  session: AceAjax.IEditSession;
  getAllEdits(): IEdit<any>[];
  getEditAtPosition(pos: AceAjax.Position): Maybe<IEdit<any>>;
  getEditsBeingProcessed(): IEdit<IBeingProcessed>[];
  getEditsToProcess(): IEdit<IToProcess>[];
  getProcessedEdits(): IEdit<IProcessed>[];
  getLastEdit(): Maybe<IEdit<IEditStage>>;
  getLastEditStop(): AceAjax.Position;
  markError(range: AceAjax.Range): void;
  moveCursorToPositionAndCenter(pos: AceAjax.Position): void;
  movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position;
  removeAllEdits(): void;
  removeEdit(e: IEdit<IEditStage>): void;
  removeEditAndFollowingOnes(e: IEdit<IEditStage>): void;
  removeFollowingEdits(e: IEdit<IEditStage>): void;
  resetEditor(s: string): void;
}

interface IEdit<S extends IEditStage> {
  array: IEditArray;
  id: number;
  previousEdit: Maybe<IEdit<any>>;
  query: string;
  stage: S;
  stage$: Rx.Observable<IEditStage>;
  startPosition: AceAjax.Position;
  stopPosition: AceAjax.Position;
  cleanup(): void;
  containsPosition(p: AceAjax.Position): boolean;
  getColor(): string;
  getPreviousStateId(): Maybe<number>;
  getProcessedStage(): Rx.IPromise<IProcessed>;
  getStateId(): Maybe<number>;
  highlight(): void;
  setStage<T extends IEditStage>(stage: T): IEdit<T>;
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
  // context: Maybe<PeaCoqContext>;
  // editId: number;
  // goals: Maybe<IGoals>;
  //status: IStatus;
  getContext(): Promise<PeaCoqContext>;
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
  setTheme(s: string): void;
  setValue(s: string, switchToTab: boolean);
}

interface IEditorError {
  error: IValueFail;
  failedEdit: IEdit<IBeingProcessed>;
  // lastValidStateId: number,
  // message: string;
  range: Maybe<AceAjax.Range>;
}
