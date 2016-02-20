class EditorTab extends Tab {
  editor: AceAjax.Editor;

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
}
