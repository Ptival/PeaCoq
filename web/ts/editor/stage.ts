import { Control } from "../sertop/command"
import { StmQuery } from "../sertop/control-command"
import { SentenceMarker } from "./sentence-marker"
import { getContextRoute } from "../peacoq/routes"
import { theme } from "../peacoq/theme"

export class ToProcess implements IToProcess {
  public marker: ISentenceMarker

  constructor(
    doc: ICoqDocument,
    start: AceAjax.Position,
    stop: AceAjax.Position
  ) {
    this.marker = new SentenceMarker(doc, start, stop)
  }

  public getColor(): string { return theme.toprocess }

  public getStateId() { return nothing() }

  public nextStageMarker(): ISentenceMarker {
    this.marker.markBeingProcessed()
    return this.marker
  }
}

export class BeingProcessed implements IBeingProcessed {
  public marker: ISentenceMarker
  public stateId: number

  constructor(e: IToProcess, sid: number) {
    this.marker = e.nextStageMarker()
    this.stateId = sid
  }

  public getColor(): string { return theme.processing }

  public getStateId() { return just(this.stateId) }

  public nextStageMarker(): ISentenceMarker {
    this.marker.markProcessed()
    return this.marker
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
  private context: Promise<PeaCoqContext> | null
  private onFulfilled: ((c: PeaCoqContext) => void) | null
  public marker: ISentenceMarker
  public stateId: number

  constructor(
    private doc: ICoqDocument,
    e: IBeingProcessed
  ) {
    this.context = null // created later
    this.onFulfilled = null
    this.marker = e.nextStageMarker()
    this.stateId = e.stateId
  }

  public getColor() { return theme.processed }

  public getContext(): Promise<PeaCoqContext> {
    // console.log("GETTING CONTEXT FOR STATE ID", this.stateId)
    if (this.context === null) {
      this.context = new Promise(onFulfilled => {
        const query = new Control(new StmQuery(
          {
            route: getContextRoute,
            sid: this.stateId,
          },
          "PeaCoqGetContext.",
          false
        ))
        this.onFulfilled = onFulfilled
        this.doc.sendCommands(Rx.Observable.just(query))
      })
    }
    return this.context
  }

  public getStateId() { return just(this.stateId) }

  public setContext(c: PeaCoqContext) {
    if (this.onFulfilled === null) {
      // someone else than getContext must have called PeaCoqGetContext
      debugger
      throw this
    }
    this.onFulfilled(c)
  }

}
