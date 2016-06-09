import * as CoqtopInput from "../coqtop-input";
import * as DebugFlags from "../debug-flags";
import { EditMarker } from "./edit-marker";
import * as Global from "../global-variables";
import * as Goal from "../goal";
import * as Goals from "../goals";
import { walkJSON } from "../peacoq/json";
import { emptyContext } from "../peacoq/peacoq";
import { PeaCoqGoal } from "../peacoq-goal";
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
  private context: Promise<PeaCoqContext>;
  marker: IEditMarker;
  stateId: number;

  constructor(
    e: IBeingProcessed,
    // this is needed so that the edit can query for its context on-demand
    private inputObserver: Rx.Observer<ICoqtopInput>
  ) {
    this.marker = e.nextStageMarker();
    this.stateId = e.stateId;
  }

  getColor() { return Theme.theme.processed; }

  getContext(): Promise<PeaCoqContext> {
    if (this.context === undefined) {
      this.context = new Promise(onFulfilled => {
        const query = new CoqtopInput.Query("PeaCoqGetContext.", this.stateId);
        query["callback"] = r => {
          if (DebugFlags.rawPeaCoqContext) { console.log(r.contents); }
          if (r.contents.length === 0) {
            onFulfilled(emptyContext);
          } else {
            // Escaping because JSON.parse sucks :(
            const safeContents = r.contents
              .replace(/\n/g, "\\n")
              .replace(/\r/g, "\\r")
              .replace(/\t/g, "\\t")
              .replace(/\f/g, "\\f");
            const c: IGoals<any> = JSON.parse(safeContents);
            const processed: PeaCoqContext = Goals.apply(
              c => {
                const pp: any = walkJSON(c.ppgoal);
                return {
                  goal: new Goal.Goal(c.goal),
                  ppgoal: new PeaCoqGoal(pp.hyps, pp.concl),
                };
              },
              c
            );
            onFulfilled(processed);
          }
        }
        this.inputObserver.onNext(query);
      });
    }
    return this.context;
  }

  getStateId() { return just(this.stateId); }

}
