class EditorTab extends Tab {
  private editor: AceAjax.Editor;

  constructor(id: string, caption: string, layout: string, panel: string) {
    super(id, caption, layout, panel);

    let self = this;

    w2ui[layout].content(panel, self.div[0]);
    this.editor = ace.edit(id + "-content");
    setupEditor(this.editor);

    this.onClickHandlers.push(function() {
      self.editor.resize();
    });

    this.onResizeHandlers.push(function() {
      self.editor.resize();
    });

    allEditorTabs.push(this);
  }

  clearValue(): void {
    this.editor.session.setValue("");
    this.captionShouldBeBold(false);
  }

  getValue(): string { return this.editor.getValue(); }

  recenter(): void {
    let pos = this.editor.getCursorPosition();
    this.editor.scrollToLine(pos.row, true, true, () => {});
  }

  setTheme(s: string): void { this.editor.setTheme(s); }

  setValue(s: string, switchToTab: boolean) {
    this.editor.session.setValue(s);
    if (switchToTab) {
      this.click();
    } else {
      this.captionShouldBeBold(true);
    }
  }

}
