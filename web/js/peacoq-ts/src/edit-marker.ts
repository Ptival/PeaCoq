import CoqDocument from "./coq85";

export default EditMarker;

export class EditMarker {
  document: CoqDocument;
  markerId: number;
  markerRange: AceAjax.Range;
  startPos: AceAjax.Position;
  stopPos: AceAjax.Position;

  constructor(doc: CoqDocument, start: AceAjax.Position, stop: AceAjax.Position) {
    this.document = doc;
    this.startPos = start;
    this.stopPos = stop;
    this.markerRange = new AceAjax.Range(start.row, start.column, stop.row, stop.column);
    this.markerId = doc.session.addMarker(this.markerRange, "toprocess", "text", false);
  }

  private mark(s: string): void {
    this.document.session.removeMarker(this.markerId);
    this.markerId = this.document.session.addMarker(this.markerRange, s, "text", false);
  }

  markProcessed(): void { this.mark("processed"); }
  markBeingProcessed(): void { this.mark("processing"); }

  remove(): void {
    this.document.session.removeMarker(this.markerId);
  }
}
