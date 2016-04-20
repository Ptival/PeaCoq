import { EditMarker } from "./edit-marker";
import * as Theme from "../theme";

export class ToProcess implements IToProcess {
  marker: IEditMarker;

  constructor(
    doc: ICoqDocument,
    start: AceAjax.Position,
    stop: AceAjax.Position
  ) {
    this.marker = new EditMarker(doc, start, stop);
  }

  getColor(): string { return Theme.theme.toprocess; }

  getStateId() { return nothing(); }

  nextStageMarker(): IEditMarker {
    this.marker.markBeingProcessed();
    return this.marker;
  }
}

export class BeingProcessed implements IBeingProcessed {
  marker: IEditMarker;
  stateId: number;

  constructor(e: IToProcess, sid: number) {
    this.marker = e.nextStageMarker();
    this.stateId = sid;
  }

  getColor(): string { return Theme.theme.processing; }

  getStateId() { return just(this.stateId); }

  nextStageMarker(): IEditMarker {
    this.marker.markProcessed();
    return this.marker;
  }
}

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

export class Processed implements IProcessed {
  context: Maybe<PeaCoqContext>;
  goals: Maybe<IGoals>;
  marker: IEditMarker;
  stateId: number;

  constructor(e: IBeingProcessed) {
    // super(e.document, e.query, e.nextStageMarker(), e.id, e.previousEdit);
    this.context = nothing(); // filled on-demand
    this.goals = nothing(); // filled on-demand
    this.marker = e.nextStageMarker();
    this.stateId = e.stateId;
  }

  getColor() { return Theme.theme.processed; }

  getStateId() { return just(this.stateId); }

}
