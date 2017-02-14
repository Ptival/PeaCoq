import { Buffer } from "./buffer"
// import { CoqDocument } from "./coq-document"
import { Editor } from "./editor"
import { KeyBindings } from "./keybindings"
import * as Stage from "./stage"

export class Workspace {
  private context: IEditor
  private document: ICoqDocument
  private editor: IBuffer

  constructor(
    private toplevel: IToplevel,
    keybindings: KeyBindings
  ) {
    this.editor = new Buffer("editor", keybindings)
    this.context = new Editor("context", keybindings)

    const keybinding$s = keybindings.getStreams()

    const sentenceToProcess$ = this.sentenceToProcess$(keybinding$s.next$)
  }

  private sentenceToProcess$(next$: Rx.Observable<{}>): Rx.Observable<ISentence<IToProcess>> {
    return next$
      .concatMap<ISentence<IToProcess>>(() => {
        const lastEditStopPos = this.editor.getLastSentenceEnd()
        const endPos = this.editor.getPositionEnd()
        const unprocessedRange: IEditorRange =
          new EditorRange(
            lastEditStopPos.row, lastEditStopPos.col,
            endPos.row, endPos.col
          )
        const unprocessedText = this.editor.getTextRange(unprocessedRange)
        if (CoqStringUtils.coqTrimLeft(unprocessedText) === "") {
          return []
        }
        const nextIndex = CoqStringUtils.next(unprocessedText)
        const newStopPos = this.editor.movePositionRight(lastEditStopPos, nextIndex)
        const query = unprocessedText.substring(0, nextIndex)
        const previousEdit = this.editor.sentences.getLast()
        const stage = new Stage.ToProcess(this, lastEditStopPos, newStopPos)
        const edit: ISentence<IToProcess> =
          this.sentences.createSentence(this, lastEditStopPos, newStopPos, query, previousEdit, stage)
        // debugger
        return [edit]
      })
      .share()
  }

}
