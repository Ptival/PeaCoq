type CommandStream<T extends ISertop.ICommand> = Rx.Observable<CommandStreamItem<T>>
type CommandStreamItem<T extends ISertop.ICommand> = Rx.Observable<T>

interface ITabs {
  pretty: ITab
  foreground: IEditorTab
  background: IEditorTab
  shelved: IEditorTab
  givenUp: IEditorTab
}

/* TODO: maybe fuse the parts of the toolbar and shortcuts that overlap? */

interface ToolbarStreams {
  fontDecrease: Rx.Observable<{}>
  fontIncrease: Rx.Observable<{}>
  goToCaret: Rx.Observable<{}>
  load: Rx.Observable<{}>
  next: Rx.Observable<{}>
  previous: Rx.Observable<{}>
  save: Rx.Observable<{}>
}

interface ShortcutsStreams {
  fontIncrease: Rx.Observable<{}>
  fontDecrease: Rx.Observable<{}>
  goToCaret: Rx.Observable<{}>
  load: Rx.Observable<{}>
  next: Rx.Observable<{}>
  previous: Rx.Observable<{}>
  save: Rx.Observable<{}>
}

interface ITab {
  div: JQuery
  click(): void
  setCaptionSuffix(s: string): void
}

interface IEditorTab extends ITab {
  clearValue(): void
  getValue(): string
  resize(): void
  setFontSize(size: number): void
  setTheme(s: string): void
  setValue(s: string, switchToTab: boolean)
}

interface IEditorError {
  error: IValueFail
  failedEdit: ISentence<IBeingProcessed>
  // lastValidStateId: number,
  // message: string
  range: Maybe<AceAjax.Range>
}
