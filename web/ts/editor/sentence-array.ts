import * as DebugFlags from "../peacoq/debug-flags"
import * as Filters from "../peacoq/filters"
import { BeingProcessed, Processed } from "./stage"
import { isBefore } from "./editor-utils"
import { Sentence } from "./sentence"
import { Strictly } from "../peacoq/strictly"

export class SentenceArray implements ISentenceArray {
  private sentences: ISentence<IStage>[]

  public sentenceChangedStage$: Rx.Subject<ISentence<IStage>>
  public sentenceCreated$: Rx.Subject<ISentence<IStage>>
  public sentenceBeingProcessed$: Rx.Observable<ISentence<IBeingProcessed>>
  public sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>
  public sentenceRemoved$: Rx.Subject<ISentence<IStage>>

  constructor(
    public document: ICoqDocument
  ) {
    this.sentences = []

    this.sentenceChangedStage$ = new Rx.Subject<any>()
    if (DebugFlags.sentenceChangedStage) {
      this.sentenceChangedStage$.subscribe(e =>
        console.log("sentence changed stage", e.stage, e)
      )
    }
    this.sentenceBeingProcessed$ =
      this.sentenceChangedStage$.let(Filters.sentenceBeingProcessed)
    this.sentenceProcessed$ =
      this.sentenceChangedStage$.let(Filters.sentenceProcessed)
    this.sentenceCreated$ = new Rx.Subject<any>()
    if (DebugFlags.sentenceCreated) { this.sentenceCreated$.subscribe(s => console.log("sentence created", s)) }
    this.sentenceRemoved$ = new Rx.Subject<any>()
    if (DebugFlags.sentenceRemoved) { this.sentenceRemoved$.subscribe(s => console.log("sentence removed", s)) }
  }

  public createSentence(
    document: ICoqDocument,
    startPosition: AceAjax.Position,
    stopPosition: AceAjax.Position,
    query: string,
    previousSentence: Maybe<ISentence<any>>,
    stage: IToProcess
  ): ISentence<IToProcess> {
    const sentence = new Sentence(this, startPosition, stopPosition, query, previousSentence, stage)
    this.sentences.push(sentence)
    this.sentenceCreated$.onNext(sentence)
    sentence.stage$.subscribe(_ => this.sentenceChangedStage$.onNext(sentence))
    return <any>sentence
  }

  public getAll(): ISentence<any>[] { return this.sentences }

  public getLast(): Maybe<ISentence<IStage>> {
    return this.sentences.length === 0 ? nothing<ISentence<IStage>>() : just(_(this.sentences).last())
  }

  public remove(r: ISentence<any>) {
    this.removeSentences(e => e.sentenceId === r.sentenceId)
  }

  public removeAll(): void {
    this.removeSentences(_ => true)
  }

  // private removeEditsFromIndex(i: number): void {
  //   if (i < 0) { debugger; }
  //   const editsToKeep = _(this.edits).slice(0, i).value()
  //   const editsToRemove = _(this.edits).slice(i, this.edits.length).value()
  //   this.edits = editsToKeep
  //   _(editsToRemove).each(e => {
  //     e.cleanup()
  //     this.editRemoved$.onNext(e)
  //   })
  // }
  //
  // removeEditAndFollowingOnes(r: ISentence<any>): void {
  //   const editIndex = _(this.edits).findIndex(r)
  //   this.removeEditsFromIndex(editIndex)
  // }
  //
  // removeFollowingEdits(r: ISentence<any>): void {
  //   const editIndex = _(this.edits).findIndex(r)
  //   this.removeEditsFromIndex(editIndex + 1)
  // }

  public removeSentences(pred: (e: ISentence<any>) => boolean): void {
    const removedSentences = ([] as ISentence<IStage>[])
    _.remove(this.sentences, e => {
      const cond = pred(e)
      if (cond) { removedSentences.push(e) }
      return cond
    })
    _(removedSentences).each(e => {
      e.cleanup()
      this.sentenceRemoved$.onNext(e)
    })
  }

}
