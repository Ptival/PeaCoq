let fontSize = 16; // pixels

export function decrement(): void { fontSize--; }

export function increment(): void { fontSize++; }

export function update(doc: ICoqDocument): void {
  doc.editor.setOption("fontSize", fontSize);
  doc.contextPanel.onFontSizeChanged(fontSize);
  jss.set("#pretty-content", { "font-size": fontSize + "px" });
  jss.set("svg body", { "font-size": fontSize + "px" });
  doc.getActiveProofTree().fmap(t => t.scheduleUpdate());
}
