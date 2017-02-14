import * as CodeMirror from "codemirror"

// import { SentenceMarker } from "./sentence-marker"

// import { KeyBindings } from "./keybindings"

// import { theme } from "../peacoq/theme"

// const CoqMode = ace.require("js/mode-coq").Mode

// export function setupEditor(e: AceAjax.Editor) {
//   console.log("FIXME CODEMIRROR")
//   // e.setTheme(theme.aceTheme)
//   // // const OCamlMode = ace.require("ace/mode/ocaml").Mode
//   // // ace.require("ace/keyboard/textarea")
//   // // e.session.setMode(new CoqMode())
//   // e.setOptions({
//   //   enableBasicAutocompletion: true,
//   //   enableLiveAutocompletion: false,
//   //   enableSnippets: false,
//   //   tabSize: 2,
//   // })
//   // e.setHighlightActiveLine(false)
//   // e.session.setUseSoftTabs(true)
//   // e.$blockScrolling = Infinity // pestering warning
// }

const codeMirrorPrefix = "Ctrl-Alt-"

function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1)
}

export class Editor implements IEditor {
  private editor: CodeMirror.Editor

  constructor(
    containerName: string,
    keybindings: IKeyBindings
  ) {
    this.editor = CodeMirror(cm => $(`#${containerName}`).append(cm), {
      lineNumbers: true,
    })
    keybindings.bindings.forEach(({ key, binding }) => {
      console.log(`Binding ${codeMirrorPrefix}${capitalize(key)}`)
      this.editor.setOption("extraKeys", {
        [`${codeMirrorPrefix}${capitalize(key)}`]: binding
      })
    })
  }

  public getPositionBegin(): IPosition {
    return thisShouldNotHappen()
  }

  public getPositionEnd(): IPosition {
    return thisShouldNotHappen()
  }

  public getTextRange(r: IEditorRange): string {
    return thisShouldNotHappen()
  }

  public markText(r: IEditorRange, klass: string): ITextMarker {
    return this.editor.getDoc().markText(
      { line: r.start.row, ch: r.start.col },
      { line: r.end.row, ch: r.end.col },
      {
        inclusiveLeft: true,
        inclusiveRight: false,
      }
    )
  }

  public movePositionRight(p: IPosition, n: number): IPosition {
    return thisShouldNotHappen()
  }

}
