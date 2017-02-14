class EditorRange implements IEditorRange {
  public start: IPosition
  public end: IPosition
  constructor(startRow: number, startCol: number, endRow: number, endCol: number) {
    this.start = { col: startCol, row: startRow }
    this.end = { col: endCol, row: endRow }
  }
}
