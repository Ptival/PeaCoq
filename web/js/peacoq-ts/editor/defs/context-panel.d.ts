interface IContextPanel {
  clear(): void;
  display(c: PeaCoqContext): void;
  onFontSizeChanged(size: number): void;
  onResize(): void;
  setTheme(theme: string): void;
}
