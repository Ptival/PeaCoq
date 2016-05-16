import * as DebugFlags from "../debug-flags";
import { Processed } from "./edit";
import { isBefore } from "./editor-utils";
import { Strictly } from "../strictly";

export class EditArray implements IEditArray {
  private edits: IEdit<IEditStage>[];

  public editChangedStage$: Rx.Subject<IEdit<IEditStage>>;
  public editCreated$: Rx.Subject<IEdit<IEditStage>>;
  public editRemoved$: Rx.Subject<IEdit<IEditStage>>;

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
    previousEdit: Maybe<IEdit<any>>,
    stage: IToProcess
  ): IEdit<IToProcess> {
    const edit = new Edit(this, startPosition, stopPosition, query, previousEdit, stage);
    this.edits.push(edit);
    this.editCreated$.onNext(edit);
    edit.stage$.subscribe(_ => this.editChangedStage$.onNext(edit));
    return <any>edit;
  }

  getAll(): IEdit<any>[] { return this.edits; }

  getLast(): Maybe<IEdit<any>> {
    return this.edits.length === 0 ? nothing() : just(_(this.edits).last());
  }

  remove(r: IEdit<any>) {
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

  removeEditAndFollowingOnes(r: IEdit<any>): void {
    const editIndex = _(this.edits).findIndex(r);
    this.removeEditsFromIndex(editIndex);
  }

  removeFollowingEdits(r: IEdit<any>): void {
    const editIndex = _(this.edits).findIndex(r);
    this.removeEditsFromIndex(editIndex + 1);
  }

}

const freshEditId = (() => {
  let id = 0;
  return () => { return id++; }
})();

/*
`stage$` should follow this success lifecycle:
onNext(IToProcess)
onNext(IBeingProcessed)
onNext(IProcessed)
onCompleted

As a consequence, `processedStage` should containt an `IProcessed`.
*/
class Edit<S extends IEditStage> implements IEdit<S> {
  private processedStage: Promise<IProcessed>;

  id: number;
  stage: S;
  stage$: Rx.Subject<S>;

  constructor(
    public array: IEditArray,
    public startPosition: AceAjax.Position,
    public stopPosition: AceAjax.Position,
    public query: string,
    public previousEdit: Maybe<IEdit<any>>,
    stage: IToProcess
  ) {
    this.id = freshEditId();
    this.stage$ = new Rx.Subject<any>();
    this.processedStage = <Promise<any>>this.stage$.toPromise();
    this.setStage(stage); // keep last
  }

  cleanup(): void {
    this.stage.marker.remove();
    this.stage$.onCompleted();
  }

  containsPosition(p: AceAjax.Position): boolean {
    // TODO: I think ace handles this
    /*
    For our purpose, an edit contains its start position, but does
    not contain its end position, so that modifications at the end
    position are allowed.
    */
    return (
      isBefore(Strictly.No, this.startPosition, p)
      && isBefore(Strictly.Yes, p, this.stopPosition)
    );
  }

  getColor(): string { return this.stage.getColor(); };

  getPreviousStateId(): Maybe<number> {
    return this.previousEdit.caseOf({
      nothing: () => just(1),
      just: (e) => e.getStateId(),
    });
  }

  getProcessedStage(): Promise<IProcessed> {
    return new Promise(onF => this.processedStage.then(v => onF(v)));
  }

  getStateId(): Maybe<number> {
    return this.stage.getStateId();
  };

  highlight(): void { this.stage.marker.highlight(); }

  setStage<T extends IEditStage>(stage: T): IEdit<T> {
    // no strong update, so circumventing the type system
    this.stage = <any>stage;
    this.stage$.onNext(this.stage);
    if (this.stage instanceof Processed) { this.stage$.onCompleted(); }
    return <any>this;
  }

  unhighlight(): void { this.stage.marker.unhighlight(); }

}
