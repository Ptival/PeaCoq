import { Processed } from "./edit";
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
  private processedStage: Promise<IProcessed>;

  commandTag: Maybe<string>;
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

  setStage<T extends IEditStage>(stage: T): ISentence<T> {
    // no strong update, so circumventing the type system
    this.stage = <any>stage;
    this.stage$.onNext(this.stage);
    if (this.stage instanceof Processed) { this.stage$.onCompleted(); }
    return <any>this;
  }

  unhighlight(): void { this.stage.marker.unhighlight(); }

}

const freshSentenceId = (() => {
  let id = 0;
  return () => { return id++; }
})();
