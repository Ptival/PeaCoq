import { setupEditor } from './editor'
import { Tab } from './tab'

export class EditorTab extends Tab {
  private editor : AceAjax.Editor

  constructor(id : string, caption : string, layout : string, panel : string) {
    super(id, caption, layout, panel)
    w2ui[layout].content(panel, this.div[0])
    this.editor = ace.edit(id + '-content')
    setupEditor(this.editor)
  }

  public clearValue() : void {
    this.editor.session.setValue('')
    this.captionShouldBeBold(false)
  }

  public getValue() : string { return this.editor.getValue() }

  public recenter() : void {
    let pos = this.editor.getCursorPosition()
    this.editor.scrollToLine(pos.row, true, true, () => { })
  }

  public resize() : void {
    this.editor.resize()
  }

  private setOption(name : string, value : any) : void {
    this.editor.setOption(name, value)
  }

  public setFontSize(size : number) : void {
    this.setOption('fontSize', size)
  }

  public setTheme(s : string) : void { this.editor.setTheme(s) }

  public setValue(s : string, switchToTab : boolean) {
    this.editor.session.setValue(s)
    if (switchToTab) {
      this.click()
    } else {
      this.captionShouldBeBold(true)
    }
  }

}
