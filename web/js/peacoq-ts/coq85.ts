var AceAnchor = ace.require("ace/anchor").Anchor;
var AceRange = ace.require("ace/range").Range;
var AceRangeList = ace.require("ace/range_list").RangeList;
var AceSelection = ace.require("ace/selection").Selection;

var pretty, foreground, background, shelved, givenUp;
var notices, warnings, errors, infos, feedback, jobs;

var nbsp = "\u00A0";

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
  removeEdits(p: (e: Edit) => boolean) {
    _.remove(this.edits, function(e) {
      var toBeRemoved = p(e);
      if (toBeRemoved) { e.removeMarker(); }
      return toBeRemoved;
    });
  }
}

var coqDocument: CoqDocument;

var statusPeriod = 3000;
var maxLength = 2000;

function onFeedback(f: Feedback) {
  var session = feedback.getSession();
  var current = session.getValue().substring(0, maxLength);
  var now = new Date();
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
  var level = m.level;

  var session;
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
    $(this).css('background-color', 'lightblue');
    e.stopImmediatePropagation();
  })
    .on('mouseout mouseleave', '.syntax', function(e) {
    $(this).css('background-color', 'transparent');
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

  var buttonGroup = $("#toolbar > .btn-group");
  addLoadLocal(buttonGroup);
  addSaveLocal(buttonGroup);
  addPrevious(buttonGroup);
  addNext(buttonGroup);
  addDebug(buttonGroup);

  var editor: AceAjax.Editor = ace.edit("editor");
  editor.session.on("change", function(c) {
    var start = c.start;
    var end = c.end;
    coqDocument.removeEdits(function(e) {
      return isAfter(e.stopPos, start);
    });
    // TODO: should probably send an EditAt to coqtop
  });

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

  var session = editor.getSession();

  setupEditor(editor);

  editor.focus();
  session.on("change", function(change) {
    killEditsAfterPosition(coqDocument, minPos(change.start, change.end));
  });

  coqDocument = new CoqDocument(editor);

  //var nbRows = ed.getSession().getLength();
  //var r0 = new Range(0, 2, 0, 5);
  //console.log(r0.toString());

  //var s = new Selection(ed.getSession());
  //s.fromOrientedRange(r0);
  //s.moveCursorBy(0, 5);
  //console.log(s.getRange().toString());
  //ed.getSession().addMarker(s.getRange(), 'coq-command', 'text');
  //var text = ed.getSession().getTextRange(s.getRange());
  //console.log(text);

  //editor.setValue("Require Import List.\nImport ListNotations.\nTheorem test : [0] = [1; 2].\n", 1);

  $(window).resize();

});

var unlockedAnchor;
var unlockedMarker;

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

var freshEditId = (function() {
  var editCounter = 2; // TODO: pick the correct number
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
    doc.pushEdit(this);
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
    e.remove();
    reportError(vf.message, true);
    errors.getSession().setValue(vf.message);
    console.log(vf.stateId);
    if (vf.stateId !== 0) {
      alert("TODO: onNextEditFail");
      // TODO: also need to cancel edits > vf.stateId
      // return peaCoqEditAt(vf.stateId);
    } else {
      return Promise.resolve();
    }
  };
}

function onNext(doc: CoqDocument) {
  clearCoqtopTabs();
  // the last anchor is how far we have processed
  var lastEditStopPos = doc.getLastEditStop();
  var endPos = doc.endAnchor.getPosition();
  var unprocessedRange =
    new AceRange(
      lastEditStopPos.row, lastEditStopPos.column,
      endPos.row, endPos.column
      );
  var unprocessedText = doc.session.getTextRange(unprocessedRange);
  if (coqTrimLeft(unprocessedText) === "") {
    return;
  }
  var nextIndex = next(unprocessedText);
  var newStopPos = movePosRight(doc, lastEditStopPos, nextIndex);
  var e = new Edit(coqDocument, lastEditStopPos, newStopPos);
  peaCoqAddPrime(unprocessedText.substring(0, nextIndex))
    .then(
    function(response) {
      e.stateId = response.stateId;
      e.markProcessed();
      doc.session.selection.clearSelection();
      doc.editor.moveCursorToPosition(newStopPos);
      doc.editor.scrollToLine(newStopPos.row, true, true, () => { });
      doc.editor.focus();
    })
    .then(updateForeground)
  // Note: it might be the case that peaCoqAddPrime succeeds, but then
  // the errors arises asynchronously in updateForeground
    .catch(onNextEditFail(e))
  ;
}

function onPrevious(doc: CoqDocument) {
  clearCoqtopTabs();
  var lastEdit = _.last(doc.edits);
  peaCoqEditAt(lastEdit.previousStateId)
    .then(() => {
    lastEdit.remove();
    doc.session.selection.clearSelection();
    doc.editor.moveCursorToPosition(lastEdit.startPos);
    doc.editor.scrollToLine(lastEdit.startPos.row, true, true, () => { });
    doc.editor.focus();
    updateForeground();
  })
    .catch(
    (vf: ValueFail) => {
      reportError(vf.message, true);
      errors.getSession().setValue(vf.message);
      updateForeground();
    })
  ;
}

type AddResult = {
  response: any;
  status: Status;
  goals: Goals;
};

function htmlPrintConstrExpr(c: ConstrExpr): string {
  var ppCmds = prConstrExpr(c);
  console.log(ppCmds);
  return htmlPrintPpCmds(ppCmds);
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

function appendPrettyPrintingToForeground(status: Status): Promise<void> {
  if (status.statusProofName === null) {
    pretty.html("");
    return Promise.resolve();
  }
  return peaCoqGetContext()
    .then(
    (context: PeaCoqContext) => {
      var currentGoal = context[0];
      pretty.html(
        htmlPrintHyps(currentGoal.hyps)
        + "<hr/>"
        + htmlPrintConstrExpr(currentGoal.concl)
        );

      /*
      Now, let's merge redundant variables on a single line
        a: nat, b: nat
      becomes:
        a, b: nat
      */

      let hyps = $(".hyp");
      // if the previous hyp has the same body/type, incorporate it
      _.forEach(hyps, function(elt, ndx) {
        if (ndx === 0) { return; }
        var prevElt = hyps[ndx - 1];
        if (sameBodyAndType(elt, prevElt)) {
          // prepend the names of the previous hyp, then delete previous
          var spanToPrependTo = $(elt).children("span")[0];
          var spanToPrependFrom = $(prevElt).children("span")[0];
          $(spanToPrependTo).html($(spanToPrependFrom).html() + ", " + $(spanToPrependTo).html());
          $(prevElt).remove();
        }
      });
      /*
      var fg = foreground.getSession();
      var old = fg.getValue();
      fg.setValue(old + "\nAs computed by PeaCoq:\n" + pp);
      */
    }
    )
    .catch(
    (error) => {
      console.log(error);
      if (error.stack) { console.log(error.stack); }
      return Promise.resolve();
    }
    )
    ;
}

function updateForeground(): Promise<any> {
  return peaCoqStatus(false)
    .then(
    (status) => {
      let promise = Promise.resolve();
      if (status.statusProofName !== null) {
        promise = promise
          .then(peaCoqGoal)
          .then(
          (goals) => {
            if (goals.fgGoals.length > 0) {
              foreground.getSession().setValue(goals.fgGoals[0].toString());
            }
          })
      } else {
      }
      promise = promise.then(() => appendPrettyPrintingToForeground(status));
      return promise;
    })
    ;
}

function onLoad(text) {
  coqDocument.removeEdits(() => true);
  coqDocument.resetEditor(text);
  resetCoqtop();
}

function loadFile() {
  var file = (<HTMLInputElement>$("#filepicker")[0]).files[0];
  var reader = new FileReader();
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
  var editor = coqDocument.editor;
  var text = editor.getValue();
  var blob = new Blob([text], { type: 'text/plain;charset=UTF-8' });
  var url = window.URL.createObjectURL(blob);
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

var delimiters = ["."];

function my_index(str) {
  var index = +Infinity;
  _(delimiters).each(function(delimiter) {
    var pos = str.indexOf(delimiter);
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

var bullets = ["{", "}", "+", "-", "*"];

function next(str) {
  // if the very next thing is one of {, }, +, -, *, it is the next
  var trimmed = coqTrimLeft(str);
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
  var lastDotPosition = coq_find_last_dot(coq_undot(str), 0);
  // now, it could be the case that there is a bullet after that dot
  var strAfterDot = str.substring(lastDotPosition + 1, str.length);
  var firstCharAfterDot = coqTrimLeft(strAfterDot)[0];
  if (_(bullets).contains(firstCharAfterDot)) {
    return lastDotPosition + 1 + strAfterDot.indexOf(firstCharAfterDot) + 1;
  }
  // otherwise, find the last dot
  return coq_find_last_dot(coq_undot(str), 0) + 1;
}

function count(str, pat) {
  var arr = str.split(pat);
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
  var index = my_index(str);
  if (index == -1) {
    return index;
  }
  var tocheck = str.substring(0, index);
  var opened = count(tocheck, "(*") + toclose - count(tocheck, "*)");
  if (opened <= 0) {
    return index;
  } else {
    var newindex = coq_find_dot(str.substring(index + 1), opened);
    if (newindex == -1) { return -1; }
    return index + newindex + 1;
  }
}

function coq_get_last_dot(str) {
  var modified = str;
  var index = -1;
  while (my_index(modified) >= 0) {
    index = my_index(modified);
    modified = modified.substring(0, index) + " " +
    modified.substring(index + 1);
  }
  return index;
}

function coq_find_last_dot(str, toopen) {
  var index = coq_get_last_dot(str);
  if (index == -1) {
    return index;
  }
  var tocheck = str.substring(index + 1);
  var closed = count(tocheck, "*)") + toopen - count(tocheck, "(*");
  if (closed <= 0) {
    return index;
  } else {
    var newindex = coq_find_last_dot(str.substring(0, index), closed);
    return newindex;
  }
}

function stripComments(s) {
  var output = "";
  var commentDepth = 0;
  var pos = 0;
  while (pos < s.length) {
    var sub = s.substring(pos);
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
  var commentDepth = 0;
  var pos = 0;
  while (pos < s.length) {
    var sub = s.substring(pos);
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
  var commentDepth = 0;
  var pos = s.length - 1;
  while (pos > 0) {
    var sub = s.substring(0, pos);
    var lastChar = sub[sub.length - 1];
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
      var screenPos = session.documentToScreenPosition(this.anchor);
      var height = config.lineHeight;
      var width = config.characterWidth;
      var top = markerLayer.$getTop(screenPos.row, config);
      var left = markerLayer.$padding + screenPos.column * width;
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
  var a = new AceAnchor(doc.session.getDocument(), row, column);
  if (insertRight) { a.$insertRight = true; }
  a.marker = {};
  a.marker.update = function(html, markerLayer, session, config) {
    var screenPos = session.documentToScreenPosition(a);
    var height = config.lineHeight;
    var width = config.characterWidth;
    var top = markerLayer.$getTop(screenPos.row, config);
    var left = markerLayer.$padding + screenPos.column * width;
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
  _.remove(doc.edits, function(edit: Edit) {
    var isAfterPosition = isAfter(edit.startPos, pos);
    //if (isAfterPosition) { rmAnchor(doc, edit.anchor); }
    return isAfterPosition;
  });
}

function movePosRight(doc: CoqDocument, pos: AceAjax.Position, n: number) {
  if (n === 0) {
    return pos;
  }
  var row = pos.row;
  var column = pos.column;
  var line = doc.session.getLine(row);
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
  //var OCamlMode = ace.require("ace/mode/ocaml").Mode;
  var CoqMode = ace.require("peacoq-js/mode-coq").Mode;
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

function addEditorTab(name: string, containerName: string): AceAjax.Editor {

  var item = $("<li>", {
    "role": "presentation",
  }).appendTo($("#" + containerName + "-pills > ul"));

  var anchor = $("<a>", {
    "href": "#" + name + "-tab",
    //"aria-controls": name + "-tab",
    //"role": "tab",
    //"data-toggle": "pill",
    "text": capitalize(name),
  })
    .appendTo(item)
    ;

  var badge = $("<span>", {
    "class": "badge",
    "id": name + "-badge",
    "html": mkGlyph("exclamation-sign"),
  })
    .css("display", "none")
    .appendTo(anchor)
    ;

  var tabPanel = $("<div>", {
    "role": "tabpanel",
    "class": "tab-pane",
    "id": name + "-tab",
  })
    .css("display", "none")
    .appendTo($("#" + containerName + "-tabs"))
    ;

  var editorDiv = $("<div>", {
    "id": name,
  })
    .appendTo(tabPanel);

  var editor = ace.edit(name);
  setupEditor(editor);

  anchor.click(function(e) {
    e.preventDefault();
    badge.css("display", "none");
    $(this).tab("show");
    $("#" + containerName + "-tabs").children(".tab-pane").css("display", "none");
    tabPanel.css("display", "flex");
    editor.resize();
    return false;
  });

  return editor;
}


function addTab(name: string, containerName: string): JQuery {

  var item = $("<li>", {
    "role": "presentation",
  }).appendTo($("#" + containerName + "-pills > ul"));

  var anchor = $("<a>", {
    "href": "#" + name + "-tab",
    //"aria-controls": name + "-tab",
    //"role": "tab",
    //"data-toggle": "pill",
    "text": capitalize(name),
  })
    .appendTo(item)
    ;

  var badge = $("<span>", {
    "class": "badge",
    "id": name + "-badge",
    "html": mkGlyph("exclamation-sign"),
  })
    .css("display", "none")
    .appendTo(anchor)
    ;

  var tabPanel = $("<div>", {
    "role": "tabpanel",
    "class": "tab-pane",
    "id": name + "-tab",
  })
    .css("display", "none")
    .appendTo($("#" + containerName + "-tabs"))
    ;

  var div = $("<div>", {
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
