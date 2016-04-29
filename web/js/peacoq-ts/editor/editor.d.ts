interface ITabs {
  pretty: ITab;
  foreground: IEditorTab;
  background: IEditorTab;
  shelved: IEditorTab;
  givenUp: IEditorTab;
  notices: IEditorTab;
  warnings: IEditorTab;
  errors: IEditorTab;
  infos: IEditorTab;
  debug: IEditorTab;
  failures: IEditorTab;
  // feedback: IEditorTab;
  jobs: IEditorTab;
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
  change$: Rx.Observable<{}>;
  stageChangeObserver: Rx.Observer<{}>;
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
  getLastEditStop(): AceAjax.Position;
  markError(range: AceAjax.Range): void;
  moveCursorToPositionAndCenter(pos: AceAjax.Position): void;
  movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position;
  removeAllEdits(): void;
  removeEdit(e: IEdit<any>): void;
  removeEditAndFollowingOnes(e: IEdit<any>): void;
  resetEditor(s: string): void;
}

interface IEdit<S extends IEditStage> {
  array: IEditArray;
  id: number;
  previousEdit: Maybe<IEdit<any>>;
  query: string;
  stage: S;
  startPosition: AceAjax.Position;
  stopPosition: AceAjax.Position;
  containsPosition(p: AceAjax.Position): boolean;
  getColor(): string;
  getPreviousStateId(): Maybe<number>;
  getStateId(): Maybe<number>;
  highlight(): void;
  remove(): void;
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
  getGoals(): Promise<IGoals>;
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
