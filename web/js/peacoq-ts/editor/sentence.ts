import * as Edit from "./edit";
import { isBefore } from "./editor-utils";
import { Strictly } from "../strictly";

/*
`stage$` should follow this success lifecycle:
onNext(IToProcess)
onNext(IBeingProcessed)
onNext(IProcessed)
onCompleted

As a consequence, `processedStage` should contain an `IProcessed`.
*/
export class Sentence<S extends IEditStage> implements ISentence<S> {
  private beingProcessed$: Rx.Observable<IBeingProcessed>;
  private processed$: Rx.Observable<IProcessed>;

  commandTag: Maybe<number>;
  sentenceId: number;
  stage: S;
  stage$: Rx.Subject<S>;

  constructor(
    public array: ISentenceArray,
    public startPosition: AceAjax.Position,
    public stopPosition: AceAjax.Position,
    public query: string,
    public previousEdit: Maybe<ISentence<any>>,
    stage: IToProcess
  ) {
    this.commandTag = nothing(); // filled when Add command is created
    this.sentenceId = freshSentenceId();
    // we use a replay subject so that the observables behave like promises
    this.stage$ = new Rx.ReplaySubject<any>();
    this.beingProcessed$ = this.stage$.filter<IBeingProcessed>(s => s instanceof Edit.BeingProcessed);
    this.processed$ = this.stage$.filter<IProcessed>(s => s instanceof Edit.Processed);
    this.setStage(stage); // keep last
  }

  cleanup(): void {
    this.stage.marker.remove();
    if (!(this.stage instanceof Edit.Processed)) {
      this.stage$.onCompleted();
    } // otherwise, it should have already completed!
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

  getBeingProcessed$(): Rx.Observable<IBeingProcessed> {
    return this.beingProcessed$;
  }

  getProcessedStage(): Promise<IProcessed> {
    return this.processed$.toPromise();
  }

  getStateId(): Maybe<number> {
    return this.stage.getStateId();
  };

  highlight(): void { this.stage.marker.highlight(); }

  setStage<T extends IEditStage>(stage: T): ISentence<T> {
    // no strong update, so circumventing the type system
    this.stage = <any>stage;
    this.stage$.onNext(this.stage);
    if (this.stage instanceof Edit.Processed) { this.stage$.onCompleted(); }
    return <any>this;
  }

  unhighlight(): void { this.stage.marker.unhighlight(); }

}

const freshSentenceId = (() => {
  let id = 0;
  return () => { return id++; }
})();
