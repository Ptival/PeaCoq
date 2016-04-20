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
  // readonly feedback: IEditorTab;
  jobs: IEditorTab;
}

/* TODO: maybe fuse the parts of the toolbar and shortcuts that overlap? */

interface ToolbarStreams {
  readonly fontDecrease: Rx.Observable<{}>;
  readonly fontIncrease: Rx.Observable<{}>;
  readonly goToCaret: Rx.Observable<{}>;
  readonly load: Rx.Observable<{}>;
  readonly next: Rx.Observable<{}>;
  readonly previous: Rx.Observable<{}>;
  readonly save: Rx.Observable<{}>;
}

interface ShortcutsStreams {
  readonly fontIncrease: Rx.Observable<{}>;
  readonly fontDecrease: Rx.Observable<{}>;
  readonly goToCaret: Rx.Observable<{}>;
  readonly load: Rx.Observable<{}>;
  readonly next: Rx.Observable<{}>;
  readonly previous: Rx.Observable<{}>;
  readonly save: Rx.Observable<{}>;
}

interface IEditArray {
  readonly change$: Rx.Observable<{}>;
  createEdit(
    document: ICoqDocument,
    startPosition: AceAjax.Position,
    stopPosition: AceAjax.Position,
    query: string,
    previousEdit: Maybe<IEdit<any>>,
    stage: IToProcess
  );
  getAll(): IEdit<any>[];
  getLast(): Maybe<IEdit<any>>;
  remove(r: IEdit<any>): void;
  removeAll(): void;
  removeEditAndFollowingOnes(e: IEdit<any>): void;
  // replace(id: number, e: IEdit<any>): void;
}

interface ICoqDocument {
  readonly editor: AceAjax.Editor;
  readonly editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>;
  readonly edits: IEditArray;
  readonly endAnchor: AceAjax.Anchor;
  readonly session: AceAjax.IEditSession;
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
  readonly array: IEditArray;
  readonly id: number;
  readonly previousEdit: Maybe<IEdit<any>>;
  readonly query: string;
  readonly stage: S;
  readonly startPosition: AceAjax.Position;
  readonly stopPosition: AceAjax.Position;
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
  readonly marker: IEditMarker;
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
  context: Maybe<PeaCoqContext>;
  // editId: number;
  goals: Maybe<IGoals>;
  //status: IStatus;
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
