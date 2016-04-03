export abstract class EditStage implements IEditStage {
  edit: IEdit;
  protected marker: IEditMarker;
  constructor(e: IEdit, m: IEditMarker) {
    this.edit = e;
    this.marker = m;
  }
  getStartPosition(): AceAjax.Position { return this.marker.startPos; }
  getStopPosition(): AceAjax.Position { return this.marker.stopPos; }
  remove(): void { this.marker.remove(); }
}

export class ToProcess extends EditStage implements IToProcess {
  constructor(e: IEdit, m: IEditMarker) { super(e, m); }
  nextStageMarker(): IEditMarker {
    this.marker.markBeingProcessed();
    return this.marker;
  }
}

export class BeingProcessed extends EditStage implements IBeingProcessed {
  stateId: number;
  constructor(e: IToProcess, sid: number) {
    super(e.edit, e.nextStageMarker());
    this.stateId = sid;
  }
  nextStageMarker(): IEditMarker {
    this.marker.markProcessed();
    return this.marker;
  }
}

let freshEditId = (function() {
  let editCounter = 2; // TODO: pick the correct number
  return function() {
    return editCounter++;
  }
})();

export class Processed extends EditStage implements IProcessed {
  context: PeaCoqContext;
  editId: number;
  goals: IGoals;
  stateId: number;
  status: IStatus;

  constructor(e: IBeingProcessed) {//, s: Status, gs: Goals, c: PeaCoqContext) {
    super(e.edit, e.nextStageMarker());
    // this.context = c;
    // this.goals = gs;
    this.editId = freshEditId();
    this.stateId = e.stateId;
    // this.status = s;
  }

}
