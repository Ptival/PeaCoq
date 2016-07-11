import * as Edit from "./edit";
import { SentenceArray } from "./edit-array";
import * as Global from "./../global-variables";
import { errorUnderlineClass, theme } from "./../theme";

export class CoqDocument implements ICoqDocument {
  beginAnchor: AceAjax.Anchor;
  contextPanel: IContextPanel;
  editorChange$: Rx.Observable<AceAjax.EditorChangeEvent>;
  edits: ISentenceArray;
  endAnchor: AceAjax.Anchor;
  sentencesChanged$: Rx.Observable<{}>;
  session: AceAjax.IEditSession;

  constructor(
    public editor: AceAjax.Editor
  ) {
    const self = this;
    this.edits = new SentenceArray(this);
    // WARNING: This line must stay over calls to mkAnchor
    this.session = editor.getSession();
    this.beginAnchor = mkAnchor(this, 0, 0, "begin-marker", true);
    this.endAnchor = mkAnchor(this, 0, 0, "end-marker", false);
    this.editorChange$ =
      Rx.Observable
        .create<AceAjax.EditorChangeEvent>(observer => {
          self.session.on("change", (e) => observer.onNext(e));
        })
        .share();
    this.sentencesChanged$ = Rx.Observable.merge(
      this.edits.editCreated$,
      this.edits.editChangedStage$,
      this.edits.editRemoved$
    );
    // this.editsChange$ = this.editsChangeSubject.asObservable();
    const newEditSubject = new Rx.Subject<ISentence<IToProcess>>();
  }

  getAllSentences(): ISentence<any>[] { return this.edits.getAll(); }

  getSentenceAtPosition(pos: AceAjax.Position): Maybe<ISentence<any>> {
    const edit = _(this.getAllSentences()).find(e => e.containsPosition(pos));
    return edit ? just(edit) : nothing();
  }

  getSentenceByStateId(id: StateId): Maybe<ISentence<any>> {
    const edit = _(this.getAllSentences()).find(e => e.getStateId().caseOf({
      nothing: () => false,
      just: s => s === id,
    }));
    return edit ? just(edit) : nothing();
  }

  getSentenceByTag(tag: CommandTag): Maybe<ISentence<any>> {
    const edit = _(this.getAllSentences()).find(e => e.commandTag.caseOf({
      nothing: () => false,
      just: s => s === tag,
    }));
    return edit ? just(edit) : nothing();
  }

  private getSentencesByStage(stage): ISentence<any>[] {
    return _(this.getAllSentences())
      .filter(e => { return e.stage instanceof stage; })
      .value();
  }

  getSentencesBeingProcessed(): ISentence<IBeingProcessed>[] {
    return this.getSentencesByStage(Edit.BeingProcessed);
  }

  getSentencesToProcess(): ISentence<IToProcess>[] {
    return this.getSentencesByStage(Edit.ToProcess);
  }

  getProcessedSentences(): ISentence<IProcessed>[] {
    return this.getSentencesByStage(Edit.Processed);
  }

  // getStopPositions(): AceAjax.Position[] {
  //   return _(this.editsProcessed).map(function(e) { return e.getStopPosition(); }).value();
  // }

  // getLastSentence(): Maybe<ISentence<IEditStage>> {
  //   return this.edits.getLast();
  // }

  getLastSentenceStop(): AceAjax.Position {
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

  markError(
    range: AceAjax.Range,
    clear$: Rx.Observable<{}>
  ): void {
    const markerId = this.session.addMarker(range, errorUnderlineClass, "text", false);
    this.moveCursorToPositionAndCenter(range.start);
    const markerChanged$ = this.editorChange$
      .filter(e => range.contains(e.start.row, e.start.column) || range.contains(e.end.row, e.end.column))
      .take(1);
    Rx.Observable.merge(
      markerChanged$,
      clear$
    ).subscribe(() => this.session.removeMarker(markerId));
  }

  nextSentence(next$: Rx.Observable<{}>): Rx.Observable<ISentence<IToProcess>> {
    return next$
      .concatMap<ISentence<IToProcess>>(() => {
        let lastEditStopPos = this.getLastSentenceStop();
        let endPos = this.endAnchor.getPosition();
        let unprocessedRange =
          new AceAjax.Range(
            lastEditStopPos.row, lastEditStopPos.column,
            endPos.row, endPos.column
          );
        let unprocessedText = this.session.getTextRange(unprocessedRange);
        if (CoqStringUtils.coqTrimLeft(unprocessedText) === "") {
          return [];
        }
        let nextIndex = CoqStringUtils.next(unprocessedText);
        let newStopPos = this.movePositionRight(lastEditStopPos, nextIndex);
        let query = unprocessedText.substring(0, nextIndex);
        let previousEdit = this.edits.getLast();
        let stage = new Edit.ToProcess(this, lastEditStopPos, newStopPos);
        let edit: ISentence<IToProcess> =
          this.edits.createEdit(this, lastEditStopPos, newStopPos, query, previousEdit, stage);
        // debugger;
        return [edit];
      })
      .share()
      ;
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

  removeAllSentences(): void { this.edits.removeAll(); }

  removeSentence(e: ISentence<any>): void { this.edits.remove(e); }

  // removeEditAndFollowingOnes(e: ISentence<any>): void {
  //   this.edits.removeEditAndFollowingOnes(e);
  // }

  removeSentences(pred: (e: ISentence<any>) => boolean): void {
    this.edits.removeEdits(pred);
  }

  // removeFollowingEdits(e: ISentence<any>): void {
  //   this.edits.removeFollowingEdits(e);
  // }

  removeSentencesByStateIds(ids: StateId[]): void {
    this.edits.removeEdits(e => e.getStateId().caseOf({
      nothing: () => false,
      just: id => _(ids).includes(id),
    }));
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
