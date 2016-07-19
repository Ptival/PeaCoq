import * as DebugFlags from "../debug-flags";
import { BeingProcessed, Processed } from "./edit";
import { isBefore } from "./editor-utils";
import { Sentence } from "./sentence";
import { Strictly } from "../strictly";

export class SentenceArray implements ISentenceArray {
  private edits: ISentence<IStage>[];

  public sentenceChangedStage$: Rx.Subject<ISentence<IStage>>;
  public sentenceCreated$: Rx.Subject<ISentence<IStage>>;
  public sentenceBeingProcessed$: Rx.Observable<ISentence<IBeingProcessed>>;
  public sentenceProcessed$: Rx.Observable<ISentence<IProcessed>>;
  public sentenceRemoved$: Rx.Subject<ISentence<IStage>>;

  constructor(
    public document: ICoqDocument
  ) {
    this.edits = [];

    this.sentenceChangedStage$ = new Rx.Subject<any>();
    if (DebugFlags.editChangedStage) {
      this.sentenceChangedStage$.subscribe(e =>
        console.log("edit changed stage", e.stage, e)
      );
    }
    this.sentenceBeingProcessed$ =
      this.sentenceChangedStage$.filter<ISentence<IBeingProcessed>>(e => e.stage instanceof BeingProcessed);
    this.sentenceProcessed$ =
      this.sentenceChangedStage$.filter<ISentence<IProcessed>>(e => e.stage instanceof Processed);
    this.sentenceCreated$ = new Rx.Subject<any>();
    if (DebugFlags.editCreated) { this.sentenceCreated$.subscribe(s => console.log("edit created", s)); }
    this.sentenceRemoved$ = new Rx.Subject<any>();
    if (DebugFlags.editRemoved) { this.sentenceRemoved$.subscribe(s => console.log("edit removed", s)); }
  }

  createSentence(
    document: ICoqDocument,
    startPosition: AceAjax.Position,
    stopPosition: AceAjax.Position,
    query: string,
    previousSentence: Maybe<ISentence<any>>,
    stage: IToProcess
  ): ISentence<IToProcess> {
    const edit = new Sentence(this, startPosition, stopPosition, query, previousSentence, stage);
    this.edits.push(edit);
    this.sentenceCreated$.onNext(edit);
    edit.stage$.subscribe(_ => this.sentenceChangedStage$.onNext(edit));
    return <any>edit;
  }

  getAll(): ISentence<any>[] { return this.edits; }

  getLast(): Maybe<ISentence<any>> {
    return this.edits.length === 0 ? nothing() : just(_(this.edits).last());
  }

  remove(r: ISentence<any>) {
    this.removeSentences(e => e.sentenceId === r.sentenceId);
  }

  removeAll(): void {
    this.removeSentences(_ => true);
  }

  // private removeEditsFromIndex(i: number): void {
  //   if (i < 0) { debugger; }
  //   const editsToKeep = _(this.edits).slice(0, i).value();
  //   const editsToRemove = _(this.edits).slice(i, this.edits.length).value();
  //   this.edits = editsToKeep;
  //   _(editsToRemove).each(e => {
  //     e.cleanup();
  //     this.editRemoved$.onNext(e);
  //   });
  // }
  //
  // removeEditAndFollowingOnes(r: ISentence<any>): void {
  //   const editIndex = _(this.edits).findIndex(r);
  //   this.removeEditsFromIndex(editIndex);
  // }
  //
  // removeFollowingEdits(r: ISentence<any>): void {
  //   const editIndex = _(this.edits).findIndex(r);
  //   this.removeEditsFromIndex(editIndex + 1);
  // }

  removeSentences(pred: (e: ISentence<any>) => boolean): void {
    const removedEdits = [];
    _.remove(this.edits, e => {
      const cond = pred(e);
      if (cond) { removedEdits.push(e); }
      return cond;
    });
    _(removedEdits).each(e => {
      e.cleanup();
      this.sentenceRemoved$.onNext(e);
    })
  }

}
