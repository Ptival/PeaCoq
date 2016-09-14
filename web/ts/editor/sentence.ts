import * as Filters from "../peacoq/filters"
import * as Stage from "./stage"
import { isBefore } from "./editor-utils"
import { Strictly } from "../peacoq/strictly"

/*
`stage$` should follow this success lifecycle:
onNext(IToProcess)
onNext(IBeingProcessed)
onNext(IProcessed)
onCompleted

As a consequence, `processedStage` should contain an `IProcessed`.
*/
export class Sentence<S extends IStage> implements ISentence<S> {
  private beingProcessed$: Rx.Observable<IBeingProcessed>
  private processed$: Rx.Observable<IProcessed>

  public commandTag: Maybe<string>
  public completionAdded$: Rx.Subject<{}>
  public completions: { [group: string]: { [tactic: string]: PeaCoqContext } }
  public sentenceId: number
  public stage: S
  public stage$: Rx.Subject<S>

  constructor(
    public array: ISentenceArray,
    public startPosition: AceAjax.Position,
    public stopPosition: AceAjax.Position,
    public query: string,
    public previousSentence: Maybe<ISentence<any>>,
    stage: IToProcess
  ) {
    this.commandTag = nothing() // filled when Add command is created
    this.sentenceId = freshSentenceId()
    this.stage$ = new Rx.ReplaySubject<any>()
    const beingProcessedSubject = new Rx.AsyncSubject<IBeingProcessed>()
    this.beingProcessed$ = beingProcessedSubject.asObservable()
    this.stage$.let(Filters.beingProcessed)
      .take(1)
      .subscribe(beingProcessedSubject)
    const processedSubject = new Rx.AsyncSubject<IProcessed>()
    this.processed$ = processedSubject.asObservable()
    this.stage$.let(Filters.processed)
      .take(1)
      .subscribe(processedSubject)
    this.setStage(stage) // keep this line after the subscriptions
    this.completions = {}
    this.completionAdded$ = new Rx.Subject()
  }

  public addCompletion(tactic: string, group: string, context: PeaCoqContext): void {
    // console.log("Adding completion for", tactic)
    if (!(group in this.completions)) { this.completions[group] = {} }
    this.completions[group][tactic] = context
    this.completionAdded$.onNext({})
  }

  public cleanup(): void {
    this.stage.marker.remove()
    if (!(this.stage instanceof Stage.Processed)) {
      this.stage$.onCompleted()
    } // otherwise, it should have already completed!
  }

  public containsPosition(p: AceAjax.Position): boolean {
    // TODO: I think ace handles this
    /*
    For our purpose, an edit contains its start position, but does
    not contain its end position, so that modifications at the end
    position are allowed.
    */
    return (
      isBefore(Strictly.No, this.startPosition, p)
      && isBefore(Strictly.Yes, p, this.stopPosition)
    )
  }

  public getColor(): string { return this.stage.getColor() }

  public getPreviousStateId(): Maybe<number> {
    return this.previousSentence.caseOf({
      nothing: () => just(1),
      just: (e) => e.getStateId(),
    })
  }

  public getBeingProcessed$(): Rx.Observable<IBeingProcessed> {
    return this.beingProcessed$
  }

  // this is too dangerous, I'd rather use the stream version
  // getProcessedStage(): Promise<IProcessed> {
  //   // .last() transforms a completed $ into an error
  //   // otherwise, the Promise resolves with undefined!
  //   return this.processed$.last().toPromise()
  // }

  public getProcessed$(): Rx.Observable<IProcessed> {
    return this.processed$
  }

  public getStateId(): Maybe<number> {
    return this.stage.getStateId()
  }

  public highlight(): void { this.stage.marker.highlight() }

  public setStage<T extends IStage>(stage: T): ISentence<T> {
    // no strong update, so circumventing the type system
    this.stage = <any>stage
    this.stage$.onNext(this.stage)
    if (this.stage instanceof Stage.Processed) { this.stage$.onCompleted() }
    return <any>this
  }

  public unhighlight(): void { this.stage.marker.unhighlight() }

  public waitUntilProcessed(): Rx.Observable<ISentence<IProcessed>> {
    return this.getProcessed$().map(_ => <ISentence<IProcessed>><any>this)
  }

}

const freshSentenceId = (() => {
  let id = 0
  return () => { return id++ }
})()
