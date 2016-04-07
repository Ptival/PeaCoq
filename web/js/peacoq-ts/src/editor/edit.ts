import { EditMarker } from "./edit-marker";
import { ToProcess } from "./edit-stage";
import { isBefore } from "./editor-utils";
import { Strictly } from "../strictly";

const newEditSubject: Rx.Subject<IEdit> = new Rx.Subject<IEdit>();
export const newEdit$: Rx.Observable<IEdit> = newEditSubject.asObservable();
const editStageChangeSubject: Rx.Subject<IEdit> = new Rx.Subject<IEdit>();
export const editStageChange$: Rx.Observable<IEdit> = editStageChangeSubject.asObservable();
const editRemovedSubject: Rx.Subject<{}> = new Rx.Subject<{}>();
export const editRemoved$: Rx.Observable<{}> = editRemovedSubject.asObservable();

const freshEditId = (() => {
  let id = 0;
  return () => { return id++; }
})();

export class Edit implements IEdit {
  document: ICoqDocument;
  id: number;
  previousEdit: Maybe<Edit>;
  query: string;
  _stage: IEditStage;

  constructor(doc: ICoqDocument, start: AceAjax.Position, stop: AceAjax.Position, query: string) {
    this.document = doc;
    this.id = freshEditId();
    this.query = query;
    let previous = _(doc.getAllEdits()).last();
    this.previousEdit = previous ? just(previous) : nothing();
    this.stage = new ToProcess(this, new EditMarker(doc, start, stop));
    newEditSubject.onNext(this);
  }

  containsPosition(p: AceAjax.Position): boolean {
    // TODO: I think ace handles this
    /*
    For our purpose, an edit contains its start position, but does
    not contain its end position, so that modifications at the end
    position are allowed.
    */
    return (
      isBefore(Strictly.No, this.getStartPosition(), p)
      && isBefore(Strictly.Yes, p, this.getStopPosition())
    );
  }

  getPreviousStateId(): number {
    return this.previousEdit.caseOf({
      nothing: () => 1,
      just: (e) => (<IReady>e.stage).stateId,
    });
  }

  getStartPosition(): AceAjax.Position { return this.stage.getStartPosition(); }

  getStopPosition(): AceAjax.Position { return this.stage.getStopPosition(); }

  remove(): void {
    this.stage.remove();
    editRemovedSubject.onNext({});
  }
  get stage(): IEditStage { return this._stage; }
  set stage(s: IEditStage) {
    this._stage = s;
    editStageChangeSubject.onNext(this);
  }
}
