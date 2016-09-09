
export function onResize(doc: ICoqDocument): void {
  doc.editor.resize();
  doc.contextPanel.onResize();
  doc.getActiveProofTree().fmap(t => {
    const parent = $("#prooftree").parent();
    t.resize(parent.width(), parent.height());
  });
}
