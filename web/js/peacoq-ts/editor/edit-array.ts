import { Processed } from "./edit";
import { isBefore } from "./editor-utils";
import { Strictly } from "../strictly";

export class EditArray implements IEditArray {
  private changeSubject: Rx.Subject<{}>;
  change$: Rx.Observable<{}>;
  private edits: IEdit<any>[];
  private removeSubject: Rx.Subject<IEdit<any>>;
  stageChangeObserver: Rx.Observer<{}>;

  constructor(
    public document: ICoqDocument
  ) {
    this.edits = [];
    this.changeSubject = new Rx.Subject<{}>();
    this.change$ = this.changeSubject.asObservable();
    this.removeSubject = new Rx.Subject<IEdit<any>>();
    this.removeSubject.subscribe(e => e.remove()); // remove marker
    const stageChangeSubject = new Rx.Subject<{}>();
    this.stageChangeObserver = stageChangeSubject.asObserver();
    stageChangeSubject.subscribe(({}) => this.changeSubject.onNext({}));
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
    this.changeSubject.onNext({});
    return <any>edit;
  }

  getAll(): IEdit<any>[] { return this.edits; }

  getLast(): Maybe<IEdit<any>> {
    return this.edits.length === 0 ? nothing() : just(_(this.edits).last());
  }

  remove(r: IEdit<any>) {
    _(this.edits).remove(e => e.id === r.id);
    this.removeSubject.onNext(r);
    this.changeSubject.onNext({});
  }

  removeAll(): void {
    _(this.edits).each(e => this.removeSubject.onNext(e));
    this.edits = [];
    this.changeSubject.onNext({});
  }

  removeEditAndFollowingOnes(r: IEdit<any>): void {
    const editIndex = _(this.edits).findIndex(r);
    if (editIndex === -1) { debugger; }
    const editsToKeep = _(this.edits).slice(0, editIndex).value();
    const editsToRemove = _(this.edits).slice(editIndex, this.edits.length).value();
    this.edits = editsToKeep;
    _(editsToRemove).each(e => this.removeSubject.onNext(e));
    this.changeSubject.onNext({});
  }

  // replace(id: number, e: IEdit): void {
  //   const foundIndex = _(this.edits).findIndex(e => e.id === id);
  //   if (foundIndex !== -1) {
  //     this.edits[foundIndex] = e;
  //     this.changeSubject.onNext({});
  //   }
  // }

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

  remove(): void {
    this.stage.marker.remove();
  }

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
