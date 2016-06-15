import * as Edit from "./edit";
import { EditArray } from "./edit-array";
import * as Global from "./../global-variables";
import { errorUnderlineClass, theme } from "./../theme";

export class CoqDocument implements ICoqDocument {
  beginAnchor: AceAjax.Anchor;
  contextPanel: IContextPanel;
  editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>;
  edits: IEditArray;
  endAnchor: AceAjax.Anchor;
  session: AceAjax.IEditSession;

  constructor(
    public editor: AceAjax.Editor
  ) {
    const self = this;
    this.edits = new EditArray(this);
    // WARNING: This line must stay over calls to mkAnchor
    this.session = editor.getSession();
    this.beginAnchor = mkAnchor(this, 0, 0, "begin-marker", true);
    this.endAnchor = mkAnchor(this, 0, 0, "end-marker", false);
    this.editorChange$ =
      Rx.Observable
        .create<AceAjax.EditorChangeEvent>((observer) => {
          self.session.on("change", (e) => observer.onNext(e));
        })
        .share();
    // this.editsChange$ = this.editsChangeSubject.asObservable();
    const newEditSubject = new Rx.Subject<IEdit<IToProcess>>();
  }

  getAllEdits(): IEdit<any>[] { return this.edits.getAll(); }

  getEditAtPosition(pos: AceAjax.Position): Maybe<IEdit<any>> {
    const edit = _(this.getAllEdits()).find(e => e.containsPosition(pos));
    return edit ? just(edit) : nothing();
  }

  private getEditsByStage(stage): IEdit<any>[] {
    return _(this.getAllEdits())
      .filter(e => { return e.stage instanceof stage; })
      .value();
  }

  getEditsBeingProcessed(): IEdit<IBeingProcessed>[] {
    return this.getEditsByStage(Edit.BeingProcessed);
  }

  getEditsToProcess(): IEdit<IToProcess>[] {
    return this.getEditsByStage(Edit.ToProcess);
  }

  getProcessedEdits(): IEdit<IProcessed>[] {
    return this.getEditsByStage(Edit.Processed);
  }

  // getStopPositions(): AceAjax.Position[] {
  //   return _(this.editsProcessed).map(function(e) { return e.getStopPosition(); }).value();
  // }

  getLastEdit(): Maybe<IEdit<IEditStage>> {
    return this.edits.getLast();
  }

  getLastEditStop(): AceAjax.Position {
    return this.edits.getLast().caseOf({
      nothing: () => this.beginAnchor.getPosition(),
      just: last => last.stopPosition,
    });
  }

  moveCursorToPositionAndCenter(pos: AceAjax.Position): void {
    // this prevents the editor from marking selected the region jumped
    this.editor.session.selection.clearSelection();
    this.editor.moveCursorToPosition(pos);
    this.editor.scrollToLine(pos.row, true, true, () => { });
  }

  movePositionRight(pos: AceAjax.Position, n: number): AceAjax.Position {
    if (n === 0) { return pos; }
    const row = pos.row;
    const column = pos.column;
    const line = this.session.getLine(row);
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
  //   const self = this;
  //   if (this.editsToProcess.length === 0 || isJust(this.editBeingProcessed)) {
  //     return Promise.resolve();
  //   }
  //   const ebp = new EditBeingProcessed(this.editsToProcess.shift());
  //   this.editBeingProcessed = just(ebp);
  //   return (
  //     peaCoqAddPrime(ebp.query)
  //       .then((response) => {
  //         const stopPos = ebp.getStopPosition();
  //         self.session.selection.clearSelection();
  //         self.editor.moveCursorToPosition(stopPos);
  //         self.editor.scrollToLine(stopPos.row, true, true, () => { });
  //         self.editor.focus();
  //         const sid: number = response.stateId;
  //         const ls = lastStatus;
  //         const s = peaCoqStatus(false);
  //         const g = s.then(peaCoqGoal);
  //         const c = g.then(peaCoqGetContext);
  //         return Promise.all<any>([s, g, c]).then(
  //           ([s, g, c]: [Status, Goals, PeaCoqContext]) => {
  //             const e = new ProcessedEdit(ebp, sid, s, g, c);
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
    const markerId = Global.coqDocument.session.addMarker(range, errorUnderlineClass, "text", false);
    this.moveCursorToPositionAndCenter(range.start);
    const markerChangedStream = this.editorChange$
      .filter((e) => range.containsRange(AceAjax.Range.fromPoints(e.start, e.end)))
      .take(1);
    markerChangedStream.subscribe(() => {
      Global.coqDocument.session.removeMarker(markerId);
    });
  }

  recenterEditor() {
    const pos = this.editor.getCursorPosition();
    this.editor.scrollToLine(pos.row, true, true, () => { });
  }

  resetEditor(text: string) {
    this.session.setValue(text);
    this.editor.focus();
    this.editor.scrollToLine(0, true, true, () => { });
  }

  removeAllEdits(): void { this.edits.removeAll(); }

  removeEdit(e: IEdit<any>): void { this.edits.remove(e); }

  removeEditAndFollowingOnes(e: IEdit<any>): void {
    this.edits.removeEditAndFollowingOnes(e);
  }

  removeFollowingEdits(e: IEdit<any>): void {
    this.edits.removeFollowingEdits(e);
  }

  // removeEdits(
  //   predicate: (e: ProcessedEdit) => boolean,
  //   beforeRemoval?: (e: ProcessedEdit) => void
  // ) {
  //   _.remove(this.editsProcessed, function(e) {
  //     const toBeRemoved = predicate(e);
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
  const a = new AceAjax.Anchor(doc.session.getDocument(), row, column);
  if (insertRight) { a.$insertRight = true; }
  const marker = doc.session.addDynamicMarker(
    {
      update: function(html, markerLayer, session, config) {
        const screenPos = session.documentToScreenPosition(a);
        const height = config.lineHeight;
        const width = config.characterWidth;
        const top = markerLayer.$getTop(screenPos.row, config);
        const left = markerLayer.$padding + screenPos.column * width;
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
