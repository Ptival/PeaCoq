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
  markBeingProcessed(): void { this.mark("processing"); }

  remove(): void {
    this.document.session.removeMarker(this.markerId);
  }
}

class Edit {
  document: CoqDocument;
  previousEdit: Maybe<Edit>;
  query: string;
  stage: EditStage;

  constructor(doc: CoqDocument, start: AceAjax.Position, stop: AceAjax.Position, query: string) {
    this.document = doc;
    this.query = query;
    let previous = _(doc.getAllEdits()).last();
    this.previousEdit = previous ? just(previous) : nothing();
    this.stage = new EditStageToProcess(this, new EditMarker(doc, start, stop));
  }

  containsPosition(p: AceAjax.Position): boolean {
    return (
      isBefore(Strictly.No, this.getStartPosition(), p)
      && isBefore(Strictly.No, p, this.getStopPosition())
    );
  }

  getStartPosition(): AceAjax.Position { return this.stage.getStartPosition(); }
  getStopPosition(): AceAjax.Position { return this.stage.getStopPosition(); }
  remove(): void { this.stage.remove(); }
}

abstract class EditStage {
  edit: Edit;
  protected marker: EditMarker;
  constructor(e: Edit, m: EditMarker) {
    this.edit = e;
    this.marker = m;
  }
  getStartPosition(): AceAjax.Position { return this.marker.startPos; }
  getStopPosition(): AceAjax.Position { return this.marker.stopPos; }
  remove(): void { this.marker.remove(); }
}

class EditStageToProcess extends EditStage {
  constructor(e: Edit, m: EditMarker) { super(e, m); }
  nextStageMarker(): EditMarker {
    this.marker.markBeingProcessed();
    return this.marker;
  }
}

class EditStageBeingProcessed extends EditStage {
  stateId: number;
  constructor(e: EditStageToProcess, sid: number) {
    super(e.edit, e.nextStageMarker());
    this.stateId = sid;
  }
  nextStageMarker(): EditMarker {
    this.marker.markProcessed();
    return this.marker;
  }
}

class EditStageProcessed extends EditStage {
  context: PeaCoqContext;
  editId: number;
  goals: Goals;
  stateId: number;
  status: Status;

  constructor(e: EditStageBeingProcessed) {//, s: Status, gs: Goals, c: PeaCoqContext) {
    super(e.edit, e.nextStageMarker());
    // this.context = c;
    // this.goals = gs;
    this.editId = freshEditId();
    this.stateId = e.stateId;
    // this.status = s;
  }

}
