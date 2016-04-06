export class EditMarker {
  document: ICoqDocument;
  klass: string;
  markerId: number;
  markerRange: AceAjax.Range;
  startPos: AceAjax.Position;
  stopPos: AceAjax.Position;

  constructor(doc: ICoqDocument, start: AceAjax.Position, stop: AceAjax.Position) {
    this.document = doc;
    this.startPos = start;
    this.stopPos = stop;
    this.klass = "toprocess";
    this.markerRange = new AceAjax.Range(start.row, start.column, stop.row, stop.column);
    this.markerId = doc.session.addMarker(this.markerRange, this.klass, "text", false);
  }

  highlight(): void { this.updateWith("highlight"); }

  markBeingProcessed(): void { this.klass = "processing"; this.update(); }

  markProcessed(): void { this.klass = "processed"; this.update(); }

  remove(): void {
    this.document.session.removeMarker(this.markerId);
  }

  unhighlight(): void { this.update(); }

  private update(): void { this.updateWith(this.klass); }

  private updateWith(klass: string): void {
    this.document.session.removeMarker(this.markerId);
    this.markerId = this.document.session.addMarker(this.markerRange, klass, "text", false);
  }

}
