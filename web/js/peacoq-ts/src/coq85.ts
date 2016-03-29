let AceAnchor = ace.require("ace/anchor").Anchor;
let AceRange = ace.require("ace/range").Range;
// let AceRangeList = ace.require("ace/range_list").RangeList;
// let AceSelection = ace.require("ace/selection").Selection;

let autoLayout = false;

let pretty: Tab;
let foreground: EditorTab;
let background: EditorTab;
let shelved: EditorTab;
let givenUp: EditorTab;
let notices: EditorTab
let warnings: EditorTab;
let errors: EditorTab;
let infos: EditorTab;
let debug: EditorTab;
let failures: EditorTab;
let feedback: EditorTab;
let jobs: EditorTab;

let allEditorTabs: EditorTab[] = [];

let nbsp = "\u00A0";

class CoqDocument {
  beginAnchor: AceAjax.Anchor;
  editBeingProcessed: Maybe<EditBeingProcessed>;
  editor: AceAjax.Editor;
  editsProcessed: ProcessedEdit[];
  editsToProcess: EditToProcess[];
  endAnchor: AceAjax.Anchor;
  session: AceAjax.IEditSession;

  constructor(editor: AceAjax.Editor) {
    this.editor = editor;
    this.editsProcessed = [];
    this.editBeingProcessed = nothing();
    this.editsToProcess = [];
    // WARNING: This line must stay over calls to mkAnchor
    this.session = editor.getSession();
    this.session.on("change", (change) => {
      killEditsAfterPosition(this, minPos(change.start, change.end));
    });
    this.beginAnchor = mkAnchor(this, 0, 0, "begin-marker", true);
    this.endAnchor = mkAnchor(this, 0, 0, "end-marker", false);
  }

  // getStopPositions(): AceAjax.Position[] {
  //   return _(this.editsProcessed).map(function(e) { return e.getStopPosition(); }).value();
  // }

  getLastEditStop(): AceAjax.Position {
    let self = this;
    // work our way backwards
    if (this.editsToProcess.length > 0) {
      return _(this.editsToProcess).last().getStopPosition();
    }
    return this.editBeingProcessed.caseOf({
      just: (e) => e.getStopPosition(),
      nothing: () => {
        if (self.editsProcessed.length === 0) {
          return self.beginAnchor.getPosition();
        }
        return _(self.editsProcessed).last().getStopPosition();
      }
    })
  }

  onProcessEditsFailure(vf: ValueFail): Promise<any> {
    if (!(vf instanceof ValueFail)) {
      throw vf;
    }
    this.editBeingProcessed.fmap((e) => e.onRemove());
    this.editBeingProcessed = nothing();
    _(this.editsToProcess).each((e) => e.onRemove());
    this.editsToProcess = [];
    reportFailure(vf.message);
    console.log(vf.stateId);
    if (vf.stateId !== 0) {
      // TODO: also need to cancel edits > vf.stateId
      return peaCoqEditAt(vf.stateId);
    } else {
      return Promise.reject(vf);
    }
  }

  processEdits(): Promise<void> {
    let self = this;
    if (this.editsToProcess.length === 0 || isJust(this.editBeingProcessed)) {
      return Promise.resolve();
    }
    let ebp = new EditBeingProcessed(this.editsToProcess.shift());
    this.editBeingProcessed = just(ebp);
    return (
      peaCoqAddPrime(ebp.query)
        .then((response) => {
          let stopPos = ebp.getStopPosition();
          self.session.selection.clearSelection();
          self.editor.moveCursorToPosition(stopPos);
          self.editor.scrollToLine(stopPos.row, true, true, () => { });
          self.editor.focus();
          let sid: number = response.stateId;
          let ls = lastStatus;
          let s = peaCoqStatus(false);
          let g = s.then(peaCoqGoal);
          let c = g.then(peaCoqGetContext);
          return Promise.all<any>([s, g, c]).then(
            ([s, g, c]: [Status, Goals, PeaCoqContext]) => {
              let e = new ProcessedEdit(ebp, sid, s, g, c);
              self.editsProcessed.push(e);
              _(editHandlers).each((h) => h(ebp.query, sid, ls, s, g, c));
              this.editBeingProcessed = nothing();
              return self.processEdits();
            });
        })
        .catch(self.onProcessEditsFailure.bind(self))
    );
  }

  pushEdit(e: ProcessedEdit) { this.editsProcessed.push(e); }

  recenterEditor() {
    let pos = this.editor.getCursorPosition();
    this.editor.scrollToLine(pos.row, true, true, () => { });
  }

  resetEditor(text: string) {
    this.editsProcessed = [];
    this.editBeingProcessed = nothing();
    this.editsToProcess = [];
    this.session.setValue(text);
    this.editor.focus();
    this.editor.scrollToLine(0, true, true, () => { });
  }

  removeEdits(
    predicate: (e: ProcessedEdit) => boolean,
    beforeRemoval?: (e: ProcessedEdit) => void
  ) {
    _.remove(this.editsProcessed, function(e) {
      let toBeRemoved = predicate(e);
      if (toBeRemoved) {
        if (beforeRemoval) { beforeRemoval(e); }
        e.onRemove();
      }
      return toBeRemoved;
    });
  }

}

//let coqDocument: CoqDocument;

let statusPeriod = 3000;
let maxLength = 2000;

function onFeedback(f: Feedback) {
  let current = feedback.getValue().substring(0, maxLength);
  let now = new Date();
  feedback.setValue(
    "[" + now.toString().substring(16, 24) + "] " + f.toString() +
    "\n" + current,
    false
  );
}

function isQueryWarning(m: Message) {
  return (
    m.level.constructor === Warning && m.content.indexOf(
      "Query commands should not be inserted in scripts"
    ) > -1
  );
}

function onMessage(m: Message) {
  m.display();
}

function periodicallyStatus(): void {
  coqtop("status", false, true).then(function(status) {
    window.setTimeout(periodicallyStatus, statusPeriod);
  });
}

function parentHeight(): string {
  return $(this).parent().css("height");
}

function halfParentHeight(): string {
  return (parseInt($(this).parent().css("height"), 10) / 2) + "px";
}

function resetCoqtop(): Promise<any> {
  return Promise.resolve();
  // return peaCoqEditAt(1)
  //   .then(() => peaCoqAddPrime("Require Import PeaCoq.PeaCoq."))
  //   .then(() => peaCoqStatus(false));
}

function setupSyntaxHovering() {

  $(document)
    .on('mouseenter mouseover', '.syntax', function(e) {
      $(this).toggleClass('peacoq-highlight', true);
      e.stopImmediatePropagation();
    })
    .on('mouseout mouseleave', '.syntax', function(e) {
      $(this).toggleClass('peacoq-highlight', false);
      e.stopImmediatePropagation();
    })
    ;

}

let unlockedAnchor;
let unlockedMarker;

function clearCoqtopTabs(clearFailures: boolean): void {
  let tabsToClear = [foreground, background, shelved, givenUp, notices, warnings, errors, infos];
  if (clearFailures) { tabsToClear.push(failures); }
  _(tabsToClear)
    .each((et: EditorTab) => {
      et.clearValue();
    });
  pretty.div.html("");
}

let freshEditId = (function() {
  let editCounter = 2; // TODO: pick the correct number
  return function() {
    return editCounter++;
  }
})();


function reportFailure(f: string) { //, switchTab: boolean) {
  failures.setValue(f, true);
  //yif (switchTab) { failures.click(); }
}

function getPreviousEditContext(e: ProcessedEdit): Maybe<PeaCoqContext> {
  return e.previousEdit.fmap((e) => e.context);
}

/*
rejects if the command was rejected (the catch only cleans up, but
throws the error again)
*/
function onNext(doc: CoqDocument): Promise<void> {
  //clearCoqtopTabs();
  let lastEditStopPos = doc.getLastEditStop();
  let endPos = doc.endAnchor.getPosition();
  let unprocessedRange =
    new AceRange(
      lastEditStopPos.row, lastEditStopPos.column,
      endPos.row, endPos.column
    );
  let unprocessedText = doc.session.getTextRange(unprocessedRange);
  if (coqTrimLeft(unprocessedText) === "") {
    return;
  }
  let nextIndex = next(unprocessedText);
  let newStopPos = movePosRight(doc, lastEditStopPos, nextIndex);
  let query = unprocessedText.substring(0, nextIndex);
  let e1 = new EditToProcess(coqDocument, lastEditStopPos, newStopPos, query);
  doc.editsToProcess.push(e1);
  return doc.processEdits();
}

type EditHandler = (q: string, sid: number, ls: Status, s: Status, g: Goals, c: PeaCoqContext) => void;
let editHandlers: EditHandler[] = [];

// TODO: there is a better way to rewind with the new STM machinery!
function rewindToPosition(
  doc: CoqDocument,
  targetPos: AceAjax.Position
): Promise<any> {
  let lastEditStopPos = doc.getLastEditStop();
  if (isAfter(Strictly.Yes, targetPos, lastEditStopPos)
    || coqDocument.editsToProcess.length > 0
    || isJust(coqDocument.editBeingProcessed)
  ) {
    return Promise.resolve();
  } else {
    let cursorPosition = coqDocument.editor.selection.getCursor();
    let editToRewindTo = _(coqDocument.editsProcessed).find(
      (e: ProcessedEdit) => e.containsPosition(cursorPosition)
    );
    return peaCoqEditAt(editToRewindTo.stateId);
  }
}

function forwardToPosition(
  doc: CoqDocument,
  targetPos: AceAjax.Position
): Promise<void> {
  let lastEditStopPos = doc.getLastEditStop();
  if (isAfter(Strictly.Yes, lastEditStopPos, targetPos)) { return Promise.resolve(); }

  // don't move forward if there is only spaces/comments
  let range = AceRange.fromPoints(lastEditStopPos, targetPos);
  let textRange = doc.session.getDocument().getTextRange(range);
  if (coqTrim(textRange) === "") { return Promise.resolve(); }

  //console.log(lastEditStopPos, targetPos, coqTrim(textRange), textRange);

  //return onNext(doc).then(() => forwardToPosition(doc, targetPos));

  onNext(doc);
  return forwardToPosition(doc, targetPos);
}

/*
TODO: This should add all the necessary edits to be proven immediately
TODO: Currently, this loops forever if a command fails
TODO: Ideally, the cursor would not jump on completion of these edits
*/
function onGoToCaret(doc: CoqDocument): Promise<void> {
  // first, check if this is going forward or backward from the end
  // of the last edit
  let cursorPos = doc.editor.getCursorPosition();
  let lastEditStopPos = doc.getLastEditStop();
  if (isAfter(Strictly.Yes, cursorPos, lastEditStopPos)) {
    return forwardToPosition(doc, cursorPos);
  } else if (isAfter(Strictly.Yes, lastEditStopPos, cursorPos)) {
    return rewindToPosition(doc, cursorPos);
  } else {
    // no need to move
    return;
  }
}

function onPrevious(doc: CoqDocument): Promise<void> {
  //clearCoqtopTabs();
  if (isJust(doc.editBeingProcessed) || doc.editsToProcess.length > 0) {
    return Promise.resolve();
  }
  let lastEdit = _.last(doc.editsProcessed);
  if (!lastEdit) { return Promise.resolve(); }
  return (
    lastEdit.previousEdit
      .caseOf({
        nothing: () => resetCoqtop(),
        just: (pe) => {
          lastStatus = pe.status;
          return peaCoqEditAt(pe.stateId);
        },
      })
      .then(() => {
        lastEdit.remove();
        doc.session.selection.clearSelection();
        doc.editor.moveCursorToPosition(lastEdit.getStartPosition());
        doc.editor.scrollToLine(lastEdit.getStartPosition().row, true, true, () => { });
        doc.editor.focus();
        // let prevEdit = _.last(doc.edits);
        // if (prevEdit !== undefined) {
        //   updateGoals(prevEdit);
        //   updatePretty(prevEdit);
        // }
      })
      .catch((vf: ValueFail) => {
        reportFailure(vf.message);
        // Hopefully, the goals have not changed?
        /*
        let s = peaCoqStatus(false);
        let g = s.then(peaCoqGoal);
        return (
          Promise.all<any>([s, g])
            .then(
            ([s, g]: [Status, Goals]) => { return updateForeground(s, g); }
            )
          );
        */
      })
  );

}

type AddResult = {
  response: any;
  status: Status;
  goals: Goals;
};

function htmlPrintConstrExpr(c: ConstrExpr): string {
  let ppCmds = prConstrExpr(c);
  //console.log(ppCmds);
  return htmlPrintPpCmds(ppCmds);
}

function htmlPrintConstrExprDiff(c: ConstrExpr, old: ConstrExpr): string {
  let ppCmds = prConstrExpr(c);
  let oldPpCmds = prConstrExpr(old);
  console.log(ppCmds);
  //return htmlPrintPpCmds(ppCmds);
  return htmlPrintPpCmdsDiff(ppCmds, oldPpCmds);
}

function htmlPrintHyp(h: PeaCoqHyp): string {
  let result = '<span><span class="tag-variable">' + h.name + "</span></span>";
  let maybeTerm = h.maybeTerm;
  result += maybeTerm.caseOf({
    nothing: () => "",
    just: (t) => "<span>\u00A0:=\u00A0</span><span>" + htmlPrintConstrExpr(t) + "</span>",
  });
  result += (
    "<span>:\u00A0</span><span>"
    + htmlPrintConstrExpr(h.type)
    + "</span>"
  );
  return result;
}

function htmlPrintHyps(hyps: PeaCoqHyp[]): string {
  return _.reduce(hyps, (acc, elt) => {
    return acc + '<div class="hyp">' + htmlPrintHyp(elt) + "</div>";
  }, "");
}

function sameBodyAndType(hyp1: HTMLElement, hyp2: HTMLElement): boolean {
  let children1 = $(hyp1).children().slice(1);
  let children2 = $(hyp2).children().slice(1);
  if (children1.length !== children2.length) { return false; }
  for (let i in _.range(children1.length)) {
    if ($(children1[i]).html() !== $(children2[i]).html()) {
      return false;
    }
  }
  return true;
}

function countBackgroundGoals(goals: Goals): number {
  return _.reduce(
    goals.bgGoals,
    (acc, elt) => acc + elt.before.length + elt.after.length,
    0
  );
}

class Anchor {
  anchor: AceAjax.Anchor;
  marker: any;
  constructor(
    doc: CoqDocument,
    row: number, column: number, klass: string, insertRight: boolean
  ) {
    this.anchor = new AceAnchor(doc.session.getDocument(), row, column);
    if (insertRight) { this.anchor.$insertRight = true; }
    this.marker = {};
    this.marker.update = function(html, markerLayer, session, config) {
      let screenPos = session.documentToScreenPosition(this.anchor);
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
    };
    this.marker = doc.session.addDynamicMarker(this.marker, true);
    this.anchor.on("change", function() {
      doc.session._signal("changeFrontMarker");
    });
  }
}

function mkAnchor(
  doc: CoqDocument,
  row: number, column: number, klass: string, insertRight: boolean
): AceAjax.Anchor {
  let a = new AceAnchor(doc.session.getDocument(), row, column);
  if (insertRight) { a.$insertRight = true; }
  a.marker = {};
  a.marker.update = function(html, markerLayer, session, config) {
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
  };
  a.marker = doc.session.addDynamicMarker(a.marker, true);
  a.on("change", function(change, anchor) {
    doc.session._signal("changeFrontMarker");
  });
  return a;
}

enum Strictly { Yes, No };

/**
 * Checks if first argument is strictly before second argument
**/
function isBefore(flag: Strictly, pos1: AceAjax.Position, pos2: AceAjax.Position): boolean {
  if (pos1.row < pos2.row) { return true; }
  if (pos1.row > pos2.row) { return false; }
  switch (flag) {
    case Strictly.Yes: return pos1.column < pos2.column;
    case Strictly.No: return pos1.column <= pos2.column;
  };
}

function isAfter(flag: Strictly, pos1: AceAjax.Position, pos2: AceAjax.Position): boolean {
  if (pos1.row > pos2.row) { return true; }
  if (pos1.row < pos2.row) { return false; }
  switch (flag) {
    case Strictly.Yes: return pos1.column > pos2.column;
    case Strictly.No: return pos1.column >= pos2.column;
  };
}

function killEditsAfterPosition(doc: CoqDocument, pos: AceAjax.Position) {
  // we will need to rewind to the state before the oldest edit we remove
  let editToRewindTo: Maybe<ProcessedEdit> = nothing();
  // we remove all the edits that are after the position that was edited
  doc.removeEdits(
    (edit: ProcessedEdit) => isAfter(Strictly.Yes, edit.getStopPosition(), pos),
    (edit: ProcessedEdit) => {
      edit.previousEdit.caseOf({
        nothing: () => { },
        just: (pe) => {
          editToRewindTo.caseOf({
            nothing: () => { editToRewindTo = just(pe); },
            just: (e) => {
              if (pe.stateId < e.stateId) { editToRewindTo = just(pe); }
            },
          });
        },
      })
    }
  );

  editToRewindTo.caseOf({
    nothing: () => { },
    just: (e) => { peaCoqEditAt(e.stateId); }
  });

}

function movePosRight(
  doc: CoqDocument,
  pos: AceAjax.Position,
  n: number
): AceAjax.Position {
  if (n === 0) {
    return pos;
  }
  let row = pos.row;
  let column = pos.column;
  let line = doc.session.getLine(row);
  if (column < line.length) {
    return movePosRight(doc, {
      "row": row,
      "column": column + 1
    }, n - 1);
  } else if (row < doc.session.getLength()) {
    return movePosRight(doc, {
      "row": row + 1,
      "column": 0
    }, n - 1);
  } else {
    return pos;
  }
}

function minPos(pos1: AceAjax.Position, pos2: AceAjax.Position): AceAjax.Position {
  if (pos1.row < pos2.row) {
    return pos1;
  }
  if (pos2.row < pos1.row) {
    return pos2;
  }
  if (pos1.column < pos2.column) {
    return pos1;
  }
  return pos2;
}

function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1);
}

let CoqMode = ace.require("peacoq-js/mode-coq").Mode;

function setupEditor(e: AceAjax.Editor) {
  e.setTheme(Theme.theme.aceTheme);
  //let OCamlMode = ace.require("ace/mode/ocaml").Mode;

  //ace.require("ace/keyboard/textarea");
  e.session.setMode(new CoqMode());
  //e.getSession().setMode("coq");
  e.setOption("tabSize", 2);
  e.setHighlightActiveLine(false);
  e.session.setUseSoftTabs(true);
  e.$blockScrolling = Infinity; // pestering warning

}
