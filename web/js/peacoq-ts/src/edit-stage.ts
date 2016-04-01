import * as Coqtop85 from "./coqtop85";
import Edit from "./edit";
import EditMarker from "./edit-marker";

export default EditStage;

export abstract class EditStage {
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

export class ToProcess extends EditStage {
  constructor(e: Edit, m: EditMarker) { super(e, m); }
  nextStageMarker(): EditMarker {
    this.marker.markBeingProcessed();
    return this.marker;
  }
}

export class BeingProcessed extends EditStage {
  stateId: number;
  constructor(e: ToProcess, sid: number) {
    super(e.edit, e.nextStageMarker());
    this.stateId = sid;
  }
  nextStageMarker(): EditMarker {
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

export class Processed extends EditStage {
  context: Coqtop85.PeaCoqContext;
  editId: number;
  goals: Coqtop85.Goals;
  stateId: number;
  status: Coqtop85.Status;

  constructor(e: BeingProcessed) {//, s: Status, gs: Goals, c: PeaCoqContext) {
    super(e.edit, e.nextStageMarker());
    // this.context = c;
    // this.goals = gs;
    this.editId = freshEditId();
    this.stateId = e.stateId;
    // this.status = s;
  }

}
