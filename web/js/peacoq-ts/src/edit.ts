import { CoqDocument } from "./coq85";
import * as Coq85 from "./coq85";
import { EditMarker } from "./edit-marker";
import * as EditStage from "./edit-stage";
import { Strictly } from "./strictly";

export class Edit {
  document: ICoqDocument;
  previousEdit: Maybe<Edit>;
  query: string;
  stage: EditStage.EditStage;

  constructor(doc: ICoqDocument, start: AceAjax.Position, stop: AceAjax.Position, query: string) {
    this.document = doc;
    this.query = query;
    let previous = _(doc.getAllEdits()).last();
    this.previousEdit = previous ? just(previous) : nothing();
    this.stage = new EditStage.ToProcess(this, new EditMarker(doc, start, stop));
  }

  containsPosition(p: AceAjax.Position): boolean {
    // TODO: I think ace handles this
    return (
      Coq85.isBefore(Strictly.No, this.getStartPosition(), p)
      && Coq85.isBefore(Strictly.No, p, this.getStopPosition())
    );
  }

  getStartPosition(): AceAjax.Position { return this.stage.getStartPosition(); }
  getStopPosition(): AceAjax.Position { return this.stage.getStopPosition(); }
  remove(): void { this.stage.remove(); }
}
