import * as EditStage from "./edit-stage";
import * as Global from "./global-variables";
import { errorUnderlineClass, theme } from "./theme";

export class CoqDocument {
  beginAnchor: AceAjax.Anchor;
  changeStream: Rx.Observable<AceAjax.EditorChangeEvent>;
  editor: AceAjax.Editor;
  private edits: IEdit[];
  endAnchor: AceAjax.Anchor;
  session: AceAjax.IEditSession;

  constructor(editor: AceAjax.Editor) {
    let self = this;
    this.editor = editor;
    this.edits = [];
    // WARNING: This line must stay over calls to mkAnchor
    this.session = editor.getSession();
    this.beginAnchor = mkAnchor(this, 0, 0, "begin-marker", true);
    this.endAnchor = mkAnchor(this, 0, 0, "end-marker", false);
    this.changeStream =
      Rx.Observable
        .create<AceAjax.EditorChangeEvent>((observer) => {
          self.session.on("change", (e) => observer.onNext(e));
        })
        .share();
  }

  getAllEdits(): IEdit[] { return this.edits; }

  private getEditStagesInstanceOf(stage): any[] {
    return _(this.edits)
      .map((e) => e.stage)
      .filter((s) => {
        return s instanceof stage;
      })
      .value();
  }

  getEditStagesBeingProcessed(): IBeingProcessed[] {
    return this.getEditStagesInstanceOf(EditStage.BeingProcessed);
  }

  getEditStagesToProcess(): IToProcess[] {
    return this.getEditStagesInstanceOf(EditStage.ToProcess);
  }

  getEditStagesProcessed(): IProcessed[] {
    return this.getEditStagesInstanceOf(EditStage.Processed);
  }

  // getStopPositions(): AceAjax.Position[] {
  //   return _(this.editsProcessed).map(function(e) { return e.getStopPosition(); }).value();
  // }

  getLastEditStop(): AceAjax.Position {
    if (this.edits.length > 0) {
      return _(this.edits).last().getStopPosition();
    } else {
      return this.beginAnchor.getPosition();
    }
  }

  moveCursorToPositionAndCenter(pos: AceAjax.Position): void {
    this.editor.moveCursorToPosition(pos);
    this.editor.scrollToLine(pos.row, true, true, () => { });
  }

  movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position {
    if (n === 0) { return pos; }
    let row = pos.row;
    let column = pos.column;
    let line = this.session.getLine(row);
    if (column < line.length) {
      return this.movePositionRight({
        "row": row,
        "column": column + 1
      }, n - 1);
    } else if (row < this.session.getLength()) {
      return this.movePositionRight({
        "row": row + 1,
        "column": 0
      }, n - 1);
    } else {
      return pos;
    }
  }

  // onProcessEditsFailure(vf: ValueFail): Promise<any> {
  //   if (!(vf instanceof ValueFail)) {
  //     throw vf;
  //   }
  //   this.editBeingProcessed.fmap((e) => e.onRemove());
  //   this.editBeingProcessed = nothing();
  //   _(this.editsToProcess).each((e) => e.onRemove());
  //   this.editsToProcess = [];
  //   reportFailure(vf.message);
  //   console.log(vf.stateId);
  //   if (vf.stateId !== 0) {
  //     // TODO: also need to cancel edits > vf.stateId
  //     return peaCoqEditAt(vf.stateId);
  //   } else {
  //     return Promise.reject(vf);
  //   }
  // }

  // processEdits(): Promise<any> {
  //   let self = this;
  //   if (this.editsToProcess.length === 0 || isJust(this.editBeingProcessed)) {
  //     return Promise.resolve();
  //   }
  //   let ebp = new EditBeingProcessed(this.editsToProcess.shift());
  //   this.editBeingProcessed = just(ebp);
  //   return (
  //     peaCoqAddPrime(ebp.query)
  //       .then((response) => {
  //         let stopPos = ebp.getStopPosition();
  //         self.session.selection.clearSelection();
  //         self.editor.moveCursorToPosition(stopPos);
  //         self.editor.scrollToLine(stopPos.row, true, true, () => { });
  //         self.editor.focus();
  //         let sid: number = response.stateId;
  //         let ls = lastStatus;
  //         let s = peaCoqStatus(false);
  //         let g = s.then(peaCoqGoal);
  //         let c = g.then(peaCoqGetContext);
  //         return Promise.all<any>([s, g, c]).then(
  //           ([s, g, c]: [Status, Goals, PeaCoqContext]) => {
  //             let e = new ProcessedEdit(ebp, sid, s, g, c);
  //             self.editsProcessed.push(e);
  //             _(editHandlers).each((h) => h(ebp.query, sid, ls, s, g, c));
  //             this.editBeingProcessed = nothing();
  //             return self.processEdits();
  //           });
  //       })
  //       .catch(self.onProcessEditsFailure.bind(self))
  //   );
  // }

  markError(range: AceAjax.Range): void {
    let markerId = Global.coqDocument.session.addMarker(range, errorUnderlineClass, "text", false);
    this.moveCursorToPositionAndCenter(range.start);
    let markerChangedStream = this.changeStream
      .do((e) => console.log(range, AceAjax.Range.fromPoints(e.start, e.end)))
      .filter((e) => range.containsRange(AceAjax.Range.fromPoints(e.start, e.end)))
      .take(1);
    markerChangedStream.subscribe(() => {
      console.log("STILL SUBSCRIBED!");
      Global.coqDocument.session.removeMarker(markerId);
    });
  }

  pushEdit(e: IEdit) { this.edits.push(e); }

  recenterEditor() {
    let pos = this.editor.getCursorPosition();
    this.editor.scrollToLine(pos.row, true, true, () => { });
  }

  resetEditor(text: string) {
    this.session.setValue(text);
    this.editor.focus();
    this.editor.scrollToLine(0, true, true, () => { });
  }

  removeAllEdits(): void {
    _(this.edits).each((e) => e.remove());
    this.edits = [];
  }

  removeEdit(e: IEdit): void {
    e.remove();
    _(this.edits).remove(e);
  }

  removeEditsAfter(e: IEdit): void {
    let self = this;
    let editIndex = _(this.edits).findIndex(e);
    let editsToKeep = _(this.edits).slice(0, editIndex).value();
    let editsToRemove = _(this.edits).slice(editIndex, this.edits.length).value();
    this.edits = editsToKeep;
    _(editsToRemove).each((e) => self.removeEdit(e));
  }

  // removeEdits(
  //   predicate: (e: ProcessedEdit) => boolean,
  //   beforeRemoval?: (e: ProcessedEdit) => void
  // ) {
  //   _.remove(this.editsProcessed, function(e) {
  //     let toBeRemoved = predicate(e);
  //     if (toBeRemoved) {
  //       if (beforeRemoval) { beforeRemoval(e); }
  //       e.onRemove();
  //     }
  //     return toBeRemoved;
  //   });
  // }

}

function mkAnchor(
  doc: CoqDocument,
  row: number, column: number,
  klass: string, insertRight: boolean
): AceAjax.Anchor {
  let a = new AceAjax.Anchor(doc.session.getDocument(), row, column);
  if (insertRight) { a.$insertRight = true; }
  let marker = doc.session.addDynamicMarker(
    {
      update: function(html, markerLayer, session, config) {
        let screenPos = session.documentToScreenPosition(a);
        let height = config.lineHeight;
        let width = config.characterWidth;
        let top = markerLayer.$getTop(screenPos.row, config);
        let left = markerLayer.$padding + screenPos.column * width;
        html.push(
          "<div class='", klass, "' style='",
          "height:", height, "px;",
          "top:", top, "px;",
          "left:", left, "px; width:", width, "px'></div>"
        );
      }
    },
    true
  );
  a.on("change", () => doc.session._signal("changeFrontMarker"));
  return a;
}
