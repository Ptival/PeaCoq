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

interface ICoqDocument {
  changeStream: Rx.Observable<AceAjax.EditorChangeEvent>;
  editor: AceAjax.Editor;
  endAnchor: AceAjax.Anchor;
  session: AceAjax.IEditSession;
  getAllEdits(): IEdit[];
  getEditStagesBeingProcessed(): IBeingProcessed[];
  // getEditStagesProcessed(): IProcessed[];
  getEditStagesToProcess(): IToProcess[];
  getEditStagesReady(): IReady[];
  getLastEditStop(): AceAjax.Position;
  markError(range: AceAjax.Range): void;
  moveCursorToPositionAndCenter(pos: AceAjax.Position): void;
  movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position;
  pushEdit(e: IEdit): void;
  removeAllEdits(): void;
  removeEdit(e: IEdit): void;
  removeEditsAfter(e: IEdit): void;
  resetEditor(s: string): void;
}

interface IEdit {
  previousEdit: Maybe<IEdit>;
  query: string;
  stage: IEditStage;
  containsPosition(p: AceAjax.Position): boolean;
  getStartPosition(): AceAjax.Position;
  getStopPosition(): AceAjax.Position;
  remove(): void;
}

interface IEditMarker {
  startPos: AceAjax.Position;
  stopPos: AceAjax.Position;
  markBeingProcessed(): void;
  markProcessed(): void;
  remove(): void;
}

interface IEditStage {
  edit: IEdit;
  getStartPosition(): AceAjax.Position;
  getStopPosition(): AceAjax.Position;
  remove(): void;
}

interface IToProcess extends IEditStage {
  nextStageMarker(): IEditMarker;
}

interface IBeingProcessed extends IEditStage {
  stateId: number;
  nextStageMarker(): IEditMarker;
}

// Disabled, read edit-stage.ts for reason why

// interface IProcessed extends IEditStage {
//   // editId: number;
//   stateId: number;
//   nextStageMarker(): IEditMarker;
// }

interface IReady extends IEditStage {
  context: PeaCoqContext;
  // editId: number;
  goals: IGoals;
  stateId: number;
  //status: IStatus;
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
