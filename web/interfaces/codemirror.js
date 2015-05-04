/* @flow */

type DocumentPosition = {
  line: number;
  ch: number;
}

type FromTo = {
  from: DocumentPosition;
  to: DocumentPosition;
}

declare class TextMarker {
  clear(): void;
  find(): FromTo;
}

declare class LineWidget {

}

declare class Doc {
  getCursor(): DocumentPosition;
  getRange(from: DocumentPosition, to: DocumentPosition): string;
  getValue(): string;
  markText(from: DocumentPosition, to: DocumentPosition, options: Object):
    TextMarker;
  setCursor(d: DocumentPosition): void;
  setValue(s: string): void;
}

type CodeMirrorConstructor = {
  (place: Element, option: Object): CodeMirrorInstance;
}

type CodeMirrorInstance = {
  addLineWidget(line: number, node: Element): LineWidget;
  findPosH(start: DocumentPosition, amount: number, unit: string):
    DocumentPosition;
  findPosV(start: DocumentPosition, amount: number, unit: string):
    DocumentPosition;
  focus(): void;
  getDoc(): Doc;
  refresh(): void;
  scrollIntoView(what: DocumentPosition | FromTo): void;
}

declare
var CodeMirror: CodeMirrorConstructor;
