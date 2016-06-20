import * as DebugFlags from "../debug-flags";
import { Processed } from "./edit";
import { isBefore } from "./editor-utils";
import { Sentence } from "./sentence";
import { Strictly } from "../strictly";

export class SentenceArray implements ISentenceArray {
  private edits: ISentence<IEditStage>[];

  public editChangedStage$: Rx.Subject<ISentence<IEditStage>>;
  public editCreated$: Rx.Subject<ISentence<IEditStage>>;
  public editProcessed$: Rx.Observable<ISentence<IProcessed>>;
  public editRemoved$: Rx.Subject<ISentence<IEditStage>>;

  constructor(
    public document: ICoqDocument
  ) {
    this.edits = [];

    this.editChangedStage$ = new Rx.Subject<any>();
    if (DebugFlags.editChangedStage) {
      this.editChangedStage$.subscribe(e =>
        console.log("edit changed stage", e.stage, e)
      );
    }
    this.editProcessed$ =
      <Rx.Observable<ISentence<any>>>
      this.editChangedStage$
        .filter(e => e.stage instanceof Processed);
    this.editCreated$ = new Rx.Subject<any>();
    if (DebugFlags.editCreated) { subscribeAndLog(this.editCreated$, "edit created"); }
    this.editRemoved$ = new Rx.Subject<any>();
    if (DebugFlags.editRemoved) { subscribeAndLog(this.editRemoved$, "edit removed"); }
  }

  createEdit(
    document: ICoqDocument,
    startPosition: AceAjax.Position,
    stopPosition: AceAjax.Position,
    query: string,
    previousEdit: Maybe<ISentence<any>>,
    stage: IToProcess
  ): ISentence<IToProcess> {
    const edit = new Sentence(this, startPosition, stopPosition, query, previousEdit, stage);
    this.edits.push(edit);
    this.editCreated$.onNext(edit);
    edit.stage$.subscribe(_ => this.editChangedStage$.onNext(edit));
    return <any>edit;
  }

  getAll(): ISentence<any>[] { return this.edits; }

  getLast(): Maybe<ISentence<any>> {
    return this.edits.length === 0 ? nothing() : just(_(this.edits).last());
  }

  remove(r: ISentence<any>) {
    _(this.edits).remove(e => e.id === r.id);
    r.cleanup();
    this.editRemoved$.onNext(r);
  }

  removeAll(): void {
    const edits = this.edits;
    this.edits = [];
    // trying to be a little efficient here, so not calling `remove`
    _(edits).each(e => {
      e.cleanup();
      this.editRemoved$.onNext(e);
    });
  }

  private removeEditsFromIndex(i: number): void {
    if (i < 0) { debugger; }
    const editsToKeep = _(this.edits).slice(0, i).value();
    const editsToRemove = _(this.edits).slice(i, this.edits.length).value();
    this.edits = editsToKeep;
    _(editsToRemove).each(e => {
      e.cleanup();
      this.editRemoved$.onNext(e);
    });
  }

  removeEditAndFollowingOnes(r: ISentence<any>): void {
    const editIndex = _(this.edits).findIndex(r);
    this.removeEditsFromIndex(editIndex);
  }

  removeFollowingEdits(r: ISentence<any>): void {
    const editIndex = _(this.edits).findIndex(r);
    this.removeEditsFromIndex(editIndex + 1);
  }

}
