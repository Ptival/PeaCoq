import * as DebugFlags from "../debug-flags";
import { Processed } from "./edit";
import { isBefore } from "./editor-utils";
import { Strictly } from "../strictly";

export class EditArray implements IEditArray {
  change$: Rx.Observable<{}>;
  private edits: IEdit<IEditStage>[];
  private editCreatedSubject: Rx.Subject<IEdit<IEditStage>>;
  private editRemovedSubject: Rx.Subject<IEdit<IEditStage>>;
  stageChangeObserver: Rx.Observer<{}>;

  constructor(
    public document: ICoqDocument
  ) {
    this.edits = [];
    this.editRemovedSubject = new Rx.Subject<IEdit<any>>();
    const stageChangeSubject = new Rx.Subject<{}>();
    this.stageChangeObserver = stageChangeSubject.asObserver();
    this.editCreatedSubject = new Rx.Subject<IEdit<IEditStage>>();
    if (DebugFlags.editCreated) {
      subscribeAndLog(this.editCreatedSubject.asObservable());
    }
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
    this.editCreatedSubject.onNext(edit);
    return <any>edit;
  }

  getAll(): IEdit<any>[] { return this.edits; }

  getLast(): Maybe<IEdit<any>> {
    return this.edits.length === 0 ? nothing() : just(_(this.edits).last());
  }

  remove(r: IEdit<any>) {
    _(this.edits).remove(e => e.id === r.id);
    r.cleanup();
    this.editRemovedSubject.onNext(r);
  }

  removeAll(): void {
    const edits = this.edits;
    this.edits = [];
    // trying to be a little efficient here, so not calling `remove`
    _(edits).each(e => {
      e.cleanup();
      this.editRemovedSubject.onNext(e);
    });
  }

  removeEditAndFollowingOnes(r: IEdit<any>): void {
    const editIndex = _(this.edits).findIndex(r);
    if (editIndex === -1) { debugger; }
    const editsToKeep = _(this.edits).slice(0, editIndex).value();
    const editsToRemove = _(this.edits).slice(editIndex, this.edits.length).value();
    this.edits = editsToKeep;
    _(editsToRemove).each(e => {
      e.cleanup();
      this.editRemovedSubject.onNext(e);
    });
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
  id: number;
  private processedStage: Promise<IProcessed>;
  stage: S;
  stage$: Rx.Observable<S>;
  private stageObserver: Rx.Observer<S>;

  constructor(
    public array: IEditArray,
    public startPosition: AceAjax.Position,
    public stopPosition: AceAjax.Position,
    public query: string,
    public previousEdit: Maybe<IEdit<any>>,
    stage: IToProcess
  ) {
    this.id = freshEditId();
    // need to circumvent the type system here
    // this.stage = <any>stage;
    const stageSubject = new Rx.Subject<S>();
    this.stage$ = stageSubject.asObservable();
    this.stageObserver = stageSubject.asObserver();
    this.processedStage = <Promise<any>>this.stage$.toPromise();
    this.setStage(stage); // keep last
  }

  cleanup(): void {
    this.stage.marker.remove();
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

  setStage<T extends IEditStage>(stage: T): Edit<T> {
    // no strong update, so circumventing the type system
    this.stage = <any>stage;
    this.stageObserver.onNext(this.stage);
    if (this.stage instanceof Processed) {
      this.stageObserver.onCompleted();
    }
    this.array.stageChangeObserver.onNext({});
    return <any>this;
  }

  unhighlight(): void { this.stage.marker.unhighlight(); }

}
