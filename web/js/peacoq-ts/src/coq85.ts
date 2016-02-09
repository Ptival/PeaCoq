let AceAnchor = ace.require("ace/anchor").Anchor;
let AceRange = ace.require("ace/range").Range;
// let AceRangeList = ace.require("ace/range_list").RangeList;
// let AceSelection = ace.require("ace/selection").Selection;

let autoLayout = false;

let pretty, foreground, background, shelved, givenUp;
let notices, warnings, errors, infos, feedback, jobs;

let nbsp = "\u00A0";

class CoqDocument {
  editor: AceAjax.Editor;
  session: AceAjax.IEditSession;
  edits: Array<Edit>;
  beginAnchor: AceAjax.Anchor;
  endAnchor: AceAjax.Anchor;
  constructor(editor: AceAjax.Editor) {
    this.editor = editor;
    this.edits = [];
    // WARNING: This line must stay over calls to mkAnchor
    this.session = editor.getSession();
    this.beginAnchor = mkAnchor(this, 0, 0, "begin-marker", true);
    this.endAnchor = mkAnchor(this, 0, 0, "end-marker", false);
  }
  getStopPositions(): Array<AceAjax.Position> {
    return _(this.edits).map(function(e) { return e.stopPos; }).value();
  }
  getLastEditStop(): AceAjax.Position {
    if (this.edits.length === 0) { return this.beginAnchor.getPosition(); }
    return _(this.edits).last().stopPos;
  }
  pushEdit(e: Edit) { this.edits.push(e); }
  resetEditor(text: string) {
    this.edits = [];
    this.session.setValue(text);
    this.editor.focus();
    this.editor.scrollToLine(0, true, true, () => { });
  }
  removeEdits(
    predicate: (e: Edit) => boolean,
    beforeRemoval?: (e: Edit) => void
    ) {
    _.remove(this.edits, function(e) {
      let toBeRemoved = predicate(e);
      if (toBeRemoved) {
        if (beforeRemoval) { beforeRemoval(e); }
        e.removeMarker();
      }
      return toBeRemoved;
    });
  }
}

let coqDocument: CoqDocument;

let statusPeriod = 3000;
let maxLength = 2000;

function onFeedback(f: Feedback) {
  let session = feedback.getSession();
  let current = session.getValue().substring(0, maxLength);
  let now = new Date();
  session.setValue("[" + now.toString().substring(16, 24) + "] " + f.toString() +
    "\n" + current);
}

function isQueryWarning(m: Message) {
  return (
    m.level.constructor === Warning && m.content.indexOf(
      "Query commands should not be inserted in scripts"
      ) > -1
    );
}

function onMessage(m: Message) {
  let level = m.level;

  let session;
  if (level instanceof Error) { session = errors.getSession(); }
  else if (level instanceof Notice) { session = notices.getSession(); }
  else if (level instanceof Warning) { session = warnings.getSession(); }
  else if (level instanceof Info) { session = infos.getSession(); }
  else {
    throw MatchFailure("onMessage", level);
  }

  session.setValue(m.content);
  if (level instanceof Notice) {
    $("#notices-badge").css("display", "");
    $("a[href=#notices-tab]").click();
  } else if (level instanceof Warning) {
    $("#warnings-badge").css("display", "");
    if (isQueryWarning(m)) {
      coqtop("status", false, true);
    }
  }
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

function setupNavigation() {
  $("a[href=#pretty-tab]").click();
  //$("a[href=#foreground-tab]").click();
  $("a[href=#notices-tab]").click();
}

function resetCoqtop() {
  peaCoqEditAt(1)
    .then(() => peaCoqAddPrime("Require Import PeaCoq.PeaCoq."));
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

/*
I can't seem to make Ace properly bubble key events, or when they bubble,
jQuery somehow does not recognize them. So fuck it, keybindings are added
to both the page and each editor...
*/
type KeyBinding = {
  jQ: string;
  aceWin: string;
  aceMac: string;
  handler: () => void
};
let keybindings: KeyBinding[] = [
  {
    jQ: "alt+ctrl+l",
    aceWin: "Alt-Ctrl-L",
    aceMac: "Option-Command-L",
    handler: onAltCtrlL,
  },
  {
    jQ: "alt+ctrl+s",
    aceWin: "Alt-Ctrl-S",
    aceMac: "Option-Command-S",
    handler: saveLocal,
  },
  {
    jQ: "alt+ctrl+down",
    aceWin: "Alt-Ctrl-Down",
    aceMac: "Option-Command-Down",
    handler: () => onNext(coqDocument)
  },
  {
    jQ: "alt+ctrl+up",
    aceWin: "Alt-Ctrl-Up",
    aceMac: "Option-Command-Down",
    handler: () => onPrevious(coqDocument)
  },
  {
    jQ: "alt+ctrl+right",
    aceWin: "Alt-Ctrl-Right",
    aceMac: "Option-Command-Right",
    handler: () => onGotoCaret(coqDocument)
  },
];

$(document).ready(function() {

  $(window).resize(function() {
    $("#editor").css("height", parentHeight);
    $("#context").css("height", halfParentHeight);
    $("#coqtop").css("height", halfParentHeight);
  });

  _(keybindings).each(function(binding) {
    $(document).bind("keydown", binding.jQ, binding.handler);
  });

  resetCoqtop();

  //periodicallyStatus();

  let buttonGroup = $("#toolbar > .btn-group");
  addLoadLocal(buttonGroup);
  addSaveLocal(buttonGroup);
  addPrevious(buttonGroup);
  addNext(buttonGroup);
  addGoToCaret(buttonGroup);
  addDebug(buttonGroup);

  let editor: AceAjax.Editor = ace.edit("editor");

  pretty = addTab("pretty", "context");
  setupSyntaxHovering();
  foreground = addEditorTab("foreground", "context");
  background = addEditorTab("background", "context");
  shelved = addEditorTab("shelved", "context");
  givenUp = addEditorTab("givenup", "context");

  notices = addEditorTab("notices", "coqtop");
  warnings = addEditorTab("warnings", "coqtop");
  errors = addEditorTab("errors", "coqtop");
  infos = addEditorTab("infos", "coqtop");
  jobs = addEditorTab("jobs", "coqtop");
  feedback = addEditorTab("feedback", "coqtop");

  //jobs     = ace.edit("jobs");

  setupNavigation();

  let session = editor.getSession();

  setupEditor(editor);

  editor.focus();
  session.on("change", function(change) {
    killEditsAfterPosition(coqDocument, minPos(change.start, change.end));
  });

  coqDocument = new CoqDocument(editor);

  //let nbRows = ed.getSession().getLength();
  //let r0 = new Range(0, 2, 0, 5);
  //console.log(r0.toString());

  //let s = new Selection(ed.getSession());
  //s.fromOrientedRange(r0);
  //s.moveCursorBy(0, 5);
  //console.log(s.getRange().toString());
  //ed.getSession().addMarker(s.getRange(), 'coq-command', 'text');
  //let text = ed.getSession().getTextRange(s.getRange());
  //console.log(text);

  //editor.setValue("Require Import List.\nImport ListNotations.\nTheorem test : [0] = [1; 2].\n", 1);

  $(window).resize();

});

let unlockedAnchor;
let unlockedMarker;

function clearCoqtopTabs() {
  _([foreground, background, shelved, givenUp, notices, warnings, errors, infos])
    .each(function(editor) {
    editor.setValue("");
  });
  $(".badge").css("display", "none");
  pretty.html("");
}

class EditState { }
class EditToProcess extends EditState { }
class EditProcessing extends EditState { }
class EditProcessed extends EditState { }

let freshEditId = (function() {
  let editCounter = 2; // TODO: pick the correct number
  return function() {
    return editCounter++;
  }
})();

class Edit {
  document: CoqDocument;
  editState: EditState;
  editId: number;
  markerId: number;
  previousStateId: number;
  stateId: number;
  markerRange: AceAjax.Range;
  startPos: AceAjax.Position;
  stopPos: AceAjax.Position;
  previousEdit: Maybe<Edit>;

  // to be updated later than initialization
  status: Status;
  goals: Goals;
  context: PeaCoqContext;

  constructor(doc: CoqDocument, start: AceAjax.Position, stop: AceAjax.Position) {
    this.editState = EditToProcess;
    this.startPos = start;
    this.stopPos = stop;

    this.markerRange = new AceRange(start.row, start.column, stop.row, stop.column);

    this.editId = freshEditId();
    if (doc.edits.length > 0) {
      this.previousStateId = _.last(doc.edits).stateId;
    } else {
      this.previousStateId = 1;
    }
    this.stateId = undefined;
    this.markerId = doc.session.addMarker(this.markerRange, "processing", "text", false);

    this.document = doc;
    this.previousEdit = (
      doc.edits.length === 0
        ? new None()
        : new Some(_(doc.edits).last())
      );
    doc.pushEdit(this);

    this.goals = new Goals(undefined);
    this.context = [];
  }

  markProcessed() {
    this.document.session.removeMarker(this.markerId);
    this.markerId = this.document.session.addMarker(this.markerRange, "processed", "text", false);
  }

  removeMarker(): void {
    this.document.session.removeMarker(this.markerId);
  }

  remove(): void {
    this.removeMarker();
    _.remove(this.document.edits, this);
  }

}

function reportError(e: string, switchTab: boolean) {
  errors.getSession().setValue(e);
  $("#errors-badge").css("display", "");
  if (switchTab) { $("a[href=#errors-tab]").click(); }
}

function onNextEditFail(e: Edit): (_1: ValueFail) => Promise<any> {
  return (vf: ValueFail) => {
    if (!(vf instanceof ValueFail)) {
      throw vf;
    }
    e.remove();
    reportError(vf.message, true);
    errors.getSession().setValue(vf.message);
    console.log(vf.stateId);
    if (vf.stateId !== 0) {
      // TODO: also need to cancel edits > vf.stateId
      return peaCoqEditAt(vf.stateId);
    } else {
      return Promise.reject(vf);
    }
  };
}

function getPreviousEditContext(e: Edit): Maybe<PeaCoqContext> {
  let prevEdit = e.previousEdit;
  let oldC = new None();
  if (prevEdit instanceof Some) {
    oldC = new Some(prevEdit.some.context);
  }
  return oldC;
}

/*
rejects if the command was rejected (the catch only cleans up, but
throws the error again)
*/
function onNext(doc: CoqDocument): Promise<void> {
  clearCoqtopTabs();
  // the last anchor is how far we have processed
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
  let e = new Edit(coqDocument, lastEditStopPos, newStopPos);
  return (
    peaCoqAddPrime(unprocessedText.substring(0, nextIndex))
      .then(
      (response) => {
        e.stateId = response.stateId;
        e.markProcessed();
        doc.session.selection.clearSelection();
        doc.editor.moveCursorToPosition(newStopPos);
        doc.editor.scrollToLine(newStopPos.row, true, true, () => { });
        doc.editor.focus();
        let s = peaCoqStatus(false);
        let g = s.then(peaCoqGoal);
        let c = g.then(peaCoqGetContext);
        return Promise.all<any>([s, g, c]).then(
          ([s, g, c]) => {
            e.status = s;
            e.goals = g;
            e.context = c;
            updateGoals(e);
            updatePretty(e);
            return Promise.resolve();
          });
      })
      .catch(onNextEditFail(e))
    );
}

// TODO: there is a better way to rewind with the new STM machinery!
function rewindToPosition(
  doc: CoqDocument,
  targetPos: AceAjax.Position
  ): Promise<void> {
  let lastEditStopPos = doc.getLastEditStop();
  if (isAfter(targetPos, lastEditStopPos)) {
    return Promise.resolve();
  } else {
    return (
      onPrevious(doc)
        .then(() => rewindToPosition(doc, targetPos))
      );
  }
}

function forwardToPosition(
  doc: CoqDocument,
  targetPos: AceAjax.Position
  ): Promise<void> {
  let lastEditStopPos = doc.getLastEditStop();
  if (isAfter(lastEditStopPos, targetPos)) { return Promise.resolve(); }

  // don't move forward if there is only spaces/comments
  let range = AceRange.fromPoints(lastEditStopPos, targetPos);
  let textRange = doc.session.getDocument().getTextRange(range);
  if (coqTrim(textRange) === "") { return Promise.resolve(); }

  //console.log(lastEditStopPos, targetPos, coqTrim(textRange), textRange);

  return onNext(doc).then(() => forwardToPosition(doc, targetPos));
}

/*
TODO: This should add all the necessary edits to be proven immediately
TODO: Currently, this loops forever if a command fails
TODO: Ideally, the cursor would not jump on completion of these edits
*/
function onGotoCaret(doc: CoqDocument): Promise<void> {
  // first, check if this is going forward or backward from the end
  // of the last edit
  let cursorPos = doc.editor.getCursorPosition();
  let lastEditStopPos = doc.getLastEditStop();
  if (isAfter(cursorPos, lastEditStopPos)) {
    return forwardToPosition(doc, cursorPos);
  } else if (isAfter(lastEditStopPos, cursorPos)) {
    return rewindToPosition(doc, cursorPos);
  } else {
    // no need to move
    return;
  }
}

function onPrevious(doc: CoqDocument): Promise<void> {
  clearCoqtopTabs();
  let lastEdit = _.last(doc.edits);
  return (
    peaCoqEditAt(lastEdit.previousStateId)
      .then(
      () => {
        lastEdit.remove();
        doc.session.selection.clearSelection();
        doc.editor.moveCursorToPosition(lastEdit.startPos);
        doc.editor.scrollToLine(lastEdit.startPos.row, true, true, () => { });
        doc.editor.focus();
        let prevEdit = _.last(doc.edits);
        if (prevEdit !== undefined) {
          updateGoals(prevEdit);
          updatePretty(prevEdit);
        }
      })
      .catch(
      (vf: ValueFail) => {
        reportError(vf.message, true);
        errors.getSession().setValue(vf.message);
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
      }
      )
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
  if (maybeTerm instanceof Some) {
    result += (
      "<span>\u00A0:=\u00A0</span><span>"
      + htmlPrintConstrExpr(maybeTerm.some) + "</span>"
      );
  }
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

function updatePretty(edit: Edit): Promise<void> {
  let context = edit.context;
  // context can be empty (if you finished a focused subgoal)
  if (context.length === 0) {
    if (edit.status.statusProofName === null) {
      pretty.html("");
    }
    else if (countBackgroundGoals(edit.goals) > 0) {
      pretty.html("Subgoal solved, but background goals remain.");
    } else {
      pretty.html("All subgoals solved!");
    }
    return Promise.resolve();
  }

  pretty.html("");
  let currentGoal = context[0];
  pretty.append(currentGoal.getHTML());
}

function countBackgroundGoals(goals: Goals): number {
  return _.reduce(
    goals.bgGoals,
    (acc, elt) => acc + elt.before.length + elt.after.length,
    0
    );
}

function updateGoals(edit: Edit): void {
  let goals = edit.goals;
  $("#foreground-counter").text(" (" + goals.fgGoals.length + ")");
  $("#background-counter").text(" (" + countBackgroundGoals(goals) + ")");
  $("#shelved-counter").text(" (" + goals.shelvedGoals.length + ")");
  $("#givenup-counter").text(" (" + goals.givenUpGoals.length + ")");
  if (goals.fgGoals.length > 0) {
    foreground.getSession().setValue(goals.fgGoals[0].toString());
  }
}

function onLoad(text) {
  coqDocument.removeEdits(() => true);
  coqDocument.resetEditor(text);
  resetCoqtop();
}

function loadFile() {
  let file = (<HTMLInputElement>$("#filepicker")[0]).files[0];
  let reader = new FileReader();
  reader.onload = function(e) {
    onLoad(reader.result);
  };
  reader.readAsText(file);
}

function onAltCtrlL() {
  loadLocal();
}

function loadLocal() {
  $("#filepicker").click();
}

function addLoadLocal(buttonGroup) {
  $("<input>", {
    "id": "filepicker",
    "type": "file",
    "style": "display: none;",
  }).appendTo(buttonGroup);

  $("#filepicker").on("change", function() {
    // TODO: warning about resetting Coq/saving file
    loadFile();
    $(this).val(""); // forces change when same file is picked
  });

  $("<button>", {
    "class": "btn btn-primary",
    "html": $("<span>")
      .append(mkGlyph("floppy-open"))
      .append(nbsp + "Load"),
    "id": "load-local-button",
  })
    .appendTo(buttonGroup)
    .on("click", loadLocal);
}

function saveLocal() {
  let editor = coqDocument.editor;
  let text = editor.getValue();
  let blob = new Blob([text], { type: 'text/plain;charset=UTF-8' });
  let url = window.URL.createObjectURL(blob);
  $("#save-local-link").attr("href", url);
  $("#save-local-link")[0].click();
  editor.focus();
}

function addSaveLocal(buttonGroup) {

  $("<button>", {
    "class": "btn btn-primary",
    "id": "save-local-button",
    "html": $("<span>")
      .append(mkGlyph("floppy-save"))
      .append(nbsp + "Save"),
  })
    .appendTo(buttonGroup)
    .on("click", saveLocal)
  ;

  $("<a>", {
    "download": "output.v",
    "id": "save-local-link",
  })
    .css("display", "none")
    .appendTo(buttonGroup)
  ;

}

function mkGlyph(name) {
  return $("<i>", {
    "class": "glyphicon glyphicon-" + name,
  });
}

function addNext(buttonGroup) {
  $("<button>", {
    "id": "next",
    "class": "btn btn-primary",
  })
    .appendTo(buttonGroup)
    .on("click", function() {
    onNext(coqDocument);
  })
    .append(mkGlyph("arrow-down"))
    .append(nbsp + "Next");
}

function addDebug(buttonGroup) {
  $("<button>", {
    "id": "debug",
    "class": "btn btn-primary",
  })
    .appendTo(buttonGroup)
    .on("click", function() {
    // Do nothing
  })
    .append("Debug: ");
}

function addPrevious(buttonGroup) {
  $("<button>", {
    "id": "previous",
    "class": "btn btn-primary",
  })
    .appendTo(buttonGroup)
    .on("click", function() {
    onPrevious(coqDocument);
  })
    .append(mkGlyph("arrow-up"))
    .append(nbsp + "Prev");
}

function addGoToCaret(buttonGroup) {
  $("<button>", {
    "id": "previous",
    "class": "btn btn-primary",
  })
    .appendTo(buttonGroup)
    .on("click", function() {
    onGotoCaret(coqDocument);
  })
    .append(mkGlyph("arrow-right"))
    .append(nbsp + "To Caret");
}

let delimiters = ["."];

function my_index(str) {
  let index = +Infinity;
  _(delimiters).each(function(delimiter) {
    let pos = str.indexOf(delimiter);
    if (pos >= 0 && pos < index) {
      index = pos;
    }
  });
  if (index !== +Infinity) {
    return index;
  } else {
    return -1;
  }
}

let bullets = ["{", "}", "+", "-", "*"];

function next(str) {
  // if the very next thing is one of {, }, +, -, *, it is the next
  let trimmed = coqTrimLeft(str);
  if (_(bullets).contains(trimmed[0])) {
    return str.length - trimmed.length + 1;
  }
  // otherwise, gotta find a dot
  return coq_find_dot(coq_undot(str), 0) + 1;
}

// TODO: this is a bit hacky
function prev(str) {
  // remove the last delimiter, since we are looking for the previous one
  str = str.substring(0, str.length - 1);
  let lastDotPosition = coq_find_last_dot(coq_undot(str), 0);
  // now, it could be the case that there is a bullet after that dot
  let strAfterDot = str.substring(lastDotPosition + 1, str.length);
  let firstCharAfterDot = coqTrimLeft(strAfterDot)[0];
  if (_(bullets).contains(firstCharAfterDot)) {
    return lastDotPosition + 1 + strAfterDot.indexOf(firstCharAfterDot) + 1;
  }
  // otherwise, find the last dot
  return coq_find_last_dot(coq_undot(str), 0) + 1;
}

function count(str, pat) {
  let arr = str.split(pat);
  return (arr.length);
}

// highlight dot that are terminators as opposed to the others
function coq_undot(str) {
  str = str.replace(/[.][.][.]/g, "__."); // emphasize the last dot of ...
  str = str.replace(/[.][.]/g, "__"); // hides .. in notations
  str = str.replace(/[.][a-zA-Z1-9_\(]/g, "__"); // hides qualified identifiers
  // hide curly braces that are implicit arguments
  //str = str.replace(/\{((?:[^\.\}]|\.(?!\s))*)\}/g, "_$1_");
  // make other braces look like periods
  //str = str.replace(/[\{\}]/g, ".");
  return str;
}

function coq_find_dot(str, toclose) {
  let index = my_index(str);
  if (index == -1) {
    return index;
  }
  let tocheck = str.substring(0, index);
  let opened = count(tocheck, "(*") + toclose - count(tocheck, "*)");
  if (opened <= 0) {
    return index;
  } else {
    let newindex = coq_find_dot(str.substring(index + 1), opened);
    if (newindex == -1) { return -1; }
    return index + newindex + 1;
  }
}

function coq_get_last_dot(str) {
  let modified = str;
  let index = -1;
  while (my_index(modified) >= 0) {
    index = my_index(modified);
    modified = modified.substring(0, index) + " " +
    modified.substring(index + 1);
  }
  return index;
}

function coq_find_last_dot(str, toopen) {
  let index = coq_get_last_dot(str);
  if (index == -1) {
    return index;
  }
  let tocheck = str.substring(index + 1);
  let closed = count(tocheck, "*)") + toopen - count(tocheck, "(*");
  if (closed <= 0) {
    return index;
  } else {
    let newindex = coq_find_last_dot(str.substring(0, index), closed);
    return newindex;
  }
}

function stripComments(s) {
  let output = "";
  let commentDepth = 0;
  let pos = 0;
  while (pos < s.length) {
    let sub = s.substring(pos);
    if (sub.startsWith("(*")) {
      commentDepth++;
      pos += 2;
    } else if (sub.startsWith("*)")) {
      commentDepth--;
      pos += 2;
    } else if (commentDepth > 0) {
      pos++;
    } else {
      output += s[pos];
      pos++;
    }
  }
  return output;
}

function coqTrim(s) {
  if (s.length > 10000) {
    alert("WARNING: Performing coqTrim on large string");
  }
  return stripComments(s).trim();
}

function coqTrimLeft(s) {
  let commentDepth = 0;
  let pos = 0;
  while (pos < s.length) {
    let sub = s.substring(pos);
    if (sub.startsWith("(*")) {
      commentDepth++;
      pos += 2;
    } else if (sub.startsWith("*)")) {
      commentDepth--;
      pos += 2;
    } else if (commentDepth > 0) {
      pos++;
    } else if (sub[0] === " " || sub[0] === "\n") {
      pos++;
    } else {
      return sub;
    }
  }
  return "";
}

function coqTrimRight(s: string): string {
  let commentDepth = 0;
  let pos = s.length - 1;
  while (pos > 0) {
    let sub = s.substring(0, pos);
    let lastChar = sub[sub.length - 1];
    if (sub.endsWith("*)")) {
      commentDepth++;
      pos -= 2;
    } else if (sub.endsWith("(*")) {
      commentDepth--;
      pos -= 2;
    } else if (commentDepth > 0) {
      pos--;
    } else if (lastChar === " " || lastChar === "\n") {
      pos--;
    } else {
      return sub;
    }
  }
  return "";
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

/*
function rmAnchor(doc: CoqDocument, a: Anchor) {
  a.anchor.detach();
  doc.session.removeMarker(a.marker.id);
}
*/

function isAfter(pos1: AceAjax.Position, pos2: AceAjax.Position): boolean {
  if (pos1.row > pos2.row) { return true; }
  if (pos1.row < pos2.row) { return false; }
  return (pos1.column > pos2.column);
}

function killEditsAfterPosition(doc: CoqDocument, pos: AceAjax.Position) {
  // we will need to rewind to the state before the oldest edit we remove
  let editToRewindTo = undefined;
  // we remove all the edits that are after the position that was edited
  doc.removeEdits(
    (edit: Edit) => isAfter(edit.stopPos, pos),
    (edit: Edit) => {
    let maybeEdit = edit.previousEdit;
      if (maybeEdit instanceof Some
        && (
          editToRewindTo === undefined
          ||
          maybeEdit.some.stateId < editToRewindTo.stateId
          )
        ) {
        editToRewindTo = maybeEdit.some;
      }
    }
  );
  if (editToRewindTo !== undefined) {
    peaCoqEditAt(editToRewindTo.stateId)
      .then(
      () => {
        updateGoals(editToRewindTo);
        updatePretty(editToRewindTo);
      });
  }
}

function movePosRight(doc: CoqDocument, pos: AceAjax.Position, n: number) {
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

function setupEditor(e: AceAjax.Editor) {
  //e.setTheme("ace/theme/monokai");
  //let OCamlMode = ace.require("ace/mode/ocaml").Mode;
  let CoqMode = ace.require("peacoq-js/mode-coq").Mode;
  //ace.require("ace/keyboard/textarea");
  e.session.setMode(new CoqMode());
  //e.getSession().setMode("coq");
  e.setOption("tabSize", 2);
  e.setHighlightActiveLine(false);
  e.session.setUseSoftTabs(true);
  e.$blockScrolling = Infinity; // pestering warning

  // I should be able to use this but it is broken
  //e.setKeyboardHandler("ace/keyboard/textarea");

  _(keybindings).each(function(binding) {
    e.commands.addCommand({
      name: binding.aceWin,
      bindKey: { win: binding.aceWin, mac: binding.aceMac },
      exec: binding.handler,
    })
  });

}

function addTab(name: string, containerName: string): JQuery {

  let item = $("<li>", {
    "role": "presentation",
  }).appendTo($("#" + containerName + "-pills > ul"));

  let anchor = $("<a>", {
    "href": "#" + name + "-tab",
    //"aria-controls": name + "-tab",
    //"role": "tab",
    //"data-toggle": "pill",
  })
    .appendTo(item)
    ;

  $("<span>", { "text": capitalize(name) }).appendTo(anchor);
  $("<span>", { "id": name + "-counter" }).appendTo(anchor);

  let badge = $("<span>", {
    "class": "badge",
    "id": name + "-badge",
    "html": mkGlyph("exclamation-sign"),
  })
    .css("display", "none")
    .appendTo(anchor)
    ;

  let tabPanel = $("<div>", {
    "role": "tabpanel",
    "class": "tab-pane",
    "id": name + "-tab",
  })
    .css("display", "none")
    .appendTo($("#" + containerName + "-tabs"))
    ;

  let div = $("<div>", {
    "id": name,
  })
    .appendTo(tabPanel);

  anchor.click(function(e) {
    e.preventDefault();
    badge.css("display", "none");
    $(this).tab("show");
    $("#" + containerName + "-tabs").children(".tab-pane").css("display", "none");
    tabPanel.css("display", "flex");
    return false;
  });

  return div;
}

function addEditorTab(name: string, containerName: string): AceAjax.Editor {

  let editorDiv = addTab(name, containerName);

  let editor = ace.edit(name);
  setupEditor(editor);

  editorDiv.find("a").click(function(e) {
    editor.resize();
  });

  return editor;

}

function focusProofTreeUI() { throw "TODO"; }
function getToprove(): string { throw "TODO"; }
function studyTactics(pt: ProofTree) { throw "TODO"; }
