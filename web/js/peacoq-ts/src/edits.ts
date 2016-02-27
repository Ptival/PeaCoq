class EditMarker {
  document: CoqDocument;
  markerId: number;
  markerRange: AceAjax.Range;
  startPos: AceAjax.Position;
  stopPos: AceAjax.Position;

  constructor(doc: CoqDocument, start: AceAjax.Position, stop: AceAjax.Position) {
    this.document = doc;
    this.startPos = start;
    this.stopPos = stop;
    this.markerRange = new AceRange(start.row, start.column, stop.row, stop.column);
    this.markerId = doc.session.addMarker(this.markerRange, "toprocess", "text", false);
  }

  private mark(s: string): void {
    this.document.session.removeMarker(this.markerId);
    this.markerId = this.document.session.addMarker(this.markerRange, s, "text", false);
  }

  markProcessed(): void { this.mark("processed"); }
  markProcessing(): void { this.mark("processing"); }

  remove(): void {
    this.document.session.removeMarker(this.markerId);
  }
}

class EditToProcess {
  document: CoqDocument;
  private marker: EditMarker;
  constructor(doc: CoqDocument, start: AceAjax.Position, stop: AceAjax.Position) {
    this.document = doc;
    this.marker = new EditMarker(doc, start, stop);
  }
  promoteMarker(): EditMarker {
    this.marker.markProcessing();
    return this.marker;
  }
}

class EditBeingProcessed {
  document: CoqDocument;
  private marker: EditMarker;
  constructor(e: EditToProcess) {
    this.document = e.document;
    this.marker = e.promoteMarker();
  }
  promoteMarker(): EditMarker {
    this.marker.markProcessed();
    return this.marker;
  }
  remove(): void {
    this.marker.remove();
  }
}

class ProcessedEdit {
  context: PeaCoqContext;
  document: CoqDocument;
  editId: number;
  goals: Goals;
  private marker: EditMarker;
  previousEdit: Maybe<ProcessedEdit>;
  stateId: number;
  status: Status;

  constructor(e: EditBeingProcessed, sid: number, s: Status, gs: Goals, c: PeaCoqContext) {
    this.context = c;
    this.document = e.document;
    this.goals = gs;
    this.marker = e.promoteMarker();
    this.editId = freshEditId();
    this.stateId = sid;
    this.status = s;
    this.previousEdit = this.document.edits.length === 0 ? nothing() : just(_(this.document.edits).last());
    this.document.pushEdit(this);
  }

  getStartPosition(): AceAjax.Position { return this.marker.startPos; }

  getStopPosition(): AceAjax.Position { return this.marker.stopPos; }

  remove(): void {
    this.marker.remove();
    _.remove(this.document.edits, this);
  }

}
