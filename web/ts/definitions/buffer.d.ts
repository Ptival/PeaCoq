interface IBuffer extends IEditor {
  sentences: ISentenceArray
  getLastSentenceEnd(): IPosition
}
