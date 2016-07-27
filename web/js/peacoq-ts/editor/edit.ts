// import * as CoqtopInput from "../coqtop-input";
import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";
import * as DebugFlags from "../debug-flags";
import { EditMarker } from "./edit-marker";
import * as Global from "../global-variables";
import * as Goal from "../goal";
import * as Goals from "../goals";
import { walkJSON } from "../peacoq/json";
import { emptyContext } from "../peacoq/peacoq";
import { PeaCoqGoal } from "../peacoq-goal";
import * as Theme from "../theme";

const peaCoqGetContextRouteId = 1;

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
  private context: Promise<PeaCoqContext> | null;
  private onFulfilled: (c: PeaCoqContext) => void | null;
  marker: IEditMarker;
  stateId: number;

  constructor(
    e: IBeingProcessed,
    // this is needed so that the edit can query for its context on-demand
    private inputObserver: Rx.Observer<ISertop.ICommand>
  ) {
    this.context = null; // created later
    this.onFulfilled = null;
    this.marker = e.nextStageMarker();
    this.stateId = e.stateId;
  }

  getColor() { return Theme.theme.processed; }

  getContext(): Promise<PeaCoqContext> {
    // console.log("GETTING CONTEXT FOR STATE ID", this.stateId);
    if (this.context === null) {
      this.context = new Promise(onFulfilled => {
        const query = new Command.Control(new ControlCommand.StmQuery({
          route: peaCoqGetContextRouteId,
          sid: this.stateId,
        }, "PeaCoqGetContext."));
        this.onFulfilled = onFulfilled;
        this.inputObserver.onNext(query);
      });
    }
    return this.context;
  }

  getStateId() { return just(this.stateId); }

  setContext(c: PeaCoqContext) {
    if (this.onFulfilled === null) {
      // someone else than getContext must have called PeaCoqGetContext
      debugger;
    }
    this.onFulfilled(c);
  }

}
