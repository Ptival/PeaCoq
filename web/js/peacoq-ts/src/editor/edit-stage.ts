import * as Theme from "../theme";

export abstract class EditStage implements IEditStage {
  edit: IEdit;
  protected marker: IEditMarker;
  constructor(e: IEdit, m: IEditMarker) {
    this.edit = e;
    this.marker = m;
  }
  abstract getColor(): string;
  getStartPosition(): AceAjax.Position { return this.marker.startPos; }
  getStopPosition(): AceAjax.Position { return this.marker.stopPos; }
  highlight(): void { this.marker.highlight(); }
  remove(): void { this.marker.remove(); }
  unhighlight(): void { this.marker.unhighlight(); }
}

export class ToProcess extends EditStage implements IToProcess {
  constructor(e: IEdit, m: IEditMarker) {
    super(e, m);
  }

  getColor(): string { return Theme.theme.toprocess; }

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

  getColor(): string { return Theme.theme.processing; }

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

/*
  So, Coqtop's feedback will tell us when an edit is [Processed], but
  for the purpose of PeaCoq, we will always then query for [Goal].
  A problem is we often (but always?) receive the [Goal] response before
  the [Processed] feedback, which is annoying to keep track of as there
  might be 4 states:
  - BeingProcessed and waiting for Goal
  - BeingProcessed and Goal received
  - Processed and waiting for Goal
  - Processed and Goal received
  To simplify my life for now, I will just ignore the [Processed]
  feedback, and move the edit stage to [Ready] whenever I receive the
  [Goal] result, with the implicit assumption that a [Processed] feedback
  will show up before/after and just be ignored.
*/

export class Ready extends EditStage implements IReady {
  context: PeaCoqContext;
  // editId: number;
  goals: IGoals;
  stateId: number;

  constructor(e: IBeingProcessed, gs: IGoals, c: PeaCoqContext) {
    super(e.edit, e.nextStageMarker());
    this.context = c;
    this.goals = gs;
    // this.editId = freshEditId();
    this.stateId = e.stateId;
    // this.status = s;
  }

  getColor() { return Theme.theme.processed; }
}
