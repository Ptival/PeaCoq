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
    this.markerRange = new AceAjax.Range(start.row, start.column, stop.row, stop.column);
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

abstract class Edit {
  marker: EditMarker;
  constructor(m: EditMarker) { this.marker = m; }
  getStartPosition(): AceAjax.Position { return this.marker.startPos; }
  getStopPosition(): AceAjax.Position { return this.marker.stopPos; }
  onRemove(): void { this.marker.remove(); }
}

class EditToProcess extends Edit {
  document: CoqDocument;
  query: string;
  constructor(
    doc: CoqDocument, start: AceAjax.Position, stop: AceAjax.Position, query: string
  ) {
    super(new EditMarker(doc, start, stop));
    this.document = doc;
    this.query = query;
  }
  promoteMarker(): EditMarker {
    this.marker.markProcessing();
    return this.marker;
  }
}

class EditBeingProcessed extends Edit {
  document: CoqDocument;
  query: string;
  stateId: number;
  constructor(e: EditToProcess, sid: number) {
    super(e.promoteMarker())
    this.document = e.document;
    this.marker = e.promoteMarker();
    this.query = e.query;
    this.stateId = sid;
  }
  promoteMarker(): EditMarker {
    this.marker.markProcessed();
    return this.marker;
  }
}

class ProcessedEdit extends Edit {
  context: PeaCoqContext;
  document: CoqDocument;
  editId: number;
  goals: Goals;
  previousEdit: Maybe<ProcessedEdit>;
  stateId: number;
  status: Status;

  constructor(e: EditBeingProcessed) {//, s: Status, gs: Goals, c: PeaCoqContext) {
    super(e.promoteMarker());
    // this.context = c;
    this.document = e.document;
    // this.goals = gs;
    this.editId = freshEditId();
    this.stateId = e.stateId;
    // this.status = s;
    this.previousEdit = this.document.editsProcessed.length === 0 ? nothing() : just(_(this.document.editsProcessed).last());
  }

  containsPosition(p: AceAjax.Position): boolean {
    return (
      isBefore(Strictly.No, this.getStartPosition(), p)
      && isBefore(Strictly.No, p, this.getStopPosition())
    );
  }

  remove(): void {
    this.onRemove();
    _.remove(this.document.editsProcessed, this);
  }

}
