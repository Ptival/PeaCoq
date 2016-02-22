class EditorTab extends Tab {
  private editor: AceAjax.Editor;

  constructor(id: string, caption: string, layout: string, panel: string) {
    let self = this;
    super(id, caption, layout, panel);

    w2ui[layout].content(panel, self.div[0]);
    this.editor = ace.edit(id + "-content");
    setupEditor(this.editor);

    this.onClickHandlers.push(function() {
      self.editor.resize();
    });

    this.onResizeHandlers.push(function() {
      self.editor.resize();
    });
  }

  getValue(): string { return this.editor.getValue(); }

  setValue(s: string, switchToTab: boolean) {
    this.editor.session.setValue(s);
    if (switchToTab) {
      this.click();
    } else {
      this.captionShouldBeBold(true);
    }
  }

}
