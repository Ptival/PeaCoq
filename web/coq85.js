/// <reference path="interfaces/ace.d.ts"/>
/// <reference path="interfaces/bootstrap/bootstrap.d.ts"/>
/// <reference path="interfaces/es6-shim.d.ts"/>
/// <reference path="interfaces/lodash.d.ts"/>
/// <reference path="interfaces/jquery/jquery.d.ts"/>
/// <reference path="coqtop85.ts"/>
var Anchor = ace.require('ace/anchor').Anchor;
var Range = ace.require('ace/range').Range;
var RangeList = ace.require('ace/range_list').RangeList;
var Selection = ace.require('ace/selection').Selection;
var editor, session;
var foreground, background, shelved, givenUp;
var notices, warnings, errors, feedback, jobs;
var beginAnchor, endAnchor, anchors;
var statusPeriod = 3000;
var maxLength = 2000;
function onFeedback(f) {
    var session = feedback.getSession();
    var current = session.getValue().substring(0, maxLength);
    var now = new Date();
    session.setValue("[" + now.toString().substring(16, 24) + "] " + f.toString() +
        '\n' + current);
}
function isQueryWarning(m) {
    return (m.level.constructor === Warning && m.content.indexOf('Query commands should not be inserted in scripts') > -1);
}
function onMessage(m) {
    var session;
    switch (m.level.constructor) {
        case Error:
            session = errors.getSession();
            break;
        case Notice:
            session = notices.getSession();
            break;
        case Warning:
            session = warnings.getSession();
            break;
        default:
            throw "Unknown message level";
    }
    ;
    session.setValue(m.content);
    switch (m.level.constructor) {
        case Notice:
            $("#notices-badge").css("display", "");
            $("a[href=#notices-tab]").click();
            break;
        case Warning:
            $("#warnings-badge").css("display", "");
            if (isQueryWarning(m)) {
                coqtop("status", false, undefined, true);
            }
            break;
        default:
            break;
    }
}
function periodicallyStatus() {
    coqtop("status", false, function (status) {
        window.setTimeout(periodicallyStatus, statusPeriod);
    }, true);
}
function parentHeight() {
    return $(this).parent().css("height");
}
function halfParentHeight() {
    return (parseInt($(this).parent().css("height"), 10) / 2) + "px";
}
function setupNavigation() {
    $("a[href=#notices-tab]").click();
    $("a[href=#foreground-tab]").click();
}
$(document).ready(function () {
    $(window).resize(function () {
        $("#editor").css("height", parentHeight);
        $("#context").css("height", halfParentHeight);
        $("#coqtop").css("height", halfParentHeight);
    });
    $(document).bind("keydown", "ctrl+g", onNext);
    peaCoqEditAt(1);
    var buttonGroup = $("#toolbar > .btn-group");
    addLoadLocal(buttonGroup);
    addNext(buttonGroup);
    editor = ace.edit("editor");
    foreground = addEditorTab("foreground", "context");
    background = addEditorTab("background", "context");
    shelved = addEditorTab("shelved", "context");
    givenUp = addEditorTab("givenup", "context");
    notices = addEditorTab("notices", "coqtop");
    warnings = addEditorTab("warnings", "coqtop");
    errors = addEditorTab("errors", "coqtop");
    jobs = addEditorTab("jobs", "coqtop");
    feedback = addEditorTab("feedback", "coqtop");
    setupNavigation();
    session = editor.getSession();
    _([editor]).each(function (e) {
        e.setTheme("ace/theme/monokai");
        e.getSession().setMode("ace/mode/ocaml");
        e.getSession().setUseSoftTabs(true);
        e.$blockScrolling = Infinity;
    });
    editor.focus();
    session.on("change", function (change) {
        killAnchorsAfterPosition(minPos(change.start, change.end));
    });
    beginAnchor = mkAnchor(0, 0, "begin-marker", true);
    endAnchor = mkAnchor(0, 0, "end-marker", false);
    anchors = [];
    $(window).resize();
});
var unlockedAnchor;
var unlockedMarker;
function clearCoqtopTabs() {
    _([foreground, background, shelved, givenUp, notices, warnings])
        .each(function (editor) {
        editor.setValue("");
    });
    $(".badge").css("display", "none");
}
function onNext() {
    clearCoqtopTabs();
    var lastAnchor = _([beginAnchor]).concat(anchors).last();
    var unprocessedRange = new Range(lastAnchor.row, lastAnchor.column, endAnchor.row, endAnchor.column);
    var unprocessedText = session.getTextRange(unprocessedRange);
    if (coqTrimLeft(unprocessedText) === "") {
        return;
    }
    var nextIndex = next(unprocessedText);
    var newLocation = movePosRight(lastAnchor, nextIndex);
    var anchor = mkAnchor(newLocation.row, newLocation.column, "marker", true);
    anchors.push(anchor);
    peaCoqAddThenRefresh(unprocessedText.substring(0, nextIndex));
}
function peaCoqAddThenRefresh(q) {
    peaCoqAddPrime(q, function (response) {
        peaCoqStatus(false, function (status) {
            if (status.statusProofName !== null) {
                peaCoqGoal(function (goals) {
                    if (goals.fgGoals.length > 0) {
                        foreground.getSession().setValue(goals.fgGoals[0].toString());
                    }
                });
            }
        });
    });
}
function resetEditor(text) {
    _(anchors).each(rmAnchor);
    anchors = [];
    session.setValue(text);
    editor.focus();
}
function onLoad(text) {
    resetEditor(text);
}
function loadFile() {
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
    $("#filepicker").on("change", function () {
        loadFile();
        $(this).val("");
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
var nbsp = "\u00A0";
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
        .on("click", function () {
        onNext();
    })
        .append(mkGlyph("arrow-down"))
        .append(nbsp + "Next");
}
var delimiters = ['.'];
function my_index(str) {
    var index = +Infinity;
    _(delimiters).each(function (delimiter) {
        var pos = str.indexOf(delimiter);
        if (pos >= 0 && pos < index) {
            index = pos;
        }
    });
    if (index !== +Infinity) {
        return index;
    }
    else {
        return -1;
    }
}
var bullets = ["{", "}", "+", "-", "*"];
function next(str) {
    var trimmed = coqTrimLeft(str);
    if (_(bullets).contains(trimmed[0])) {
        return str.length - trimmed.length + 1;
    }
    return coq_find_dot(coq_undot(str), 0) + 1;
}
function prev(str) {
    var str = str.substring(0, str.length - 1);
    var lastDotPosition = coq_find_last_dot(coq_undot(str), 0);
    var strAfterDot = str.substring(lastDotPosition + 1, str.length);
    var firstCharAfterDot = coqTrimLeft(strAfterDot)[0];
    if (_(bullets).contains(firstCharAfterDot)) {
        return lastDotPosition + 1 + strAfterDot.indexOf(firstCharAfterDot) + 1;
    }
    return coq_find_last_dot(coq_undot(str), 0) + 1;
}
function count(str, pat) {
    var arr = str.split(pat);
    return (arr.length);
}
function coq_undot(str) {
    str = str.replace(/[.][.][.]/g, '__.');
    str = str.replace(/[.][.]/g, '__');
    str = str.replace(/[.][a-zA-Z1-9_\(]/g, '__');
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
    }
    else {
        var newindex = coq_find_dot(str.substring(index + 1), opened);
        if (newindex == -1)
            return -1;
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
    }
    else {
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
        }
        else if (sub.startsWith("*)")) {
            commentDepth--;
            pos += 2;
        }
        else if (commentDepth > 0) {
            pos++;
        }
        else {
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
        }
        else if (sub.startsWith("*)")) {
            commentDepth--;
            pos += 2;
        }
        else if (commentDepth > 0) {
            pos++;
        }
        else if (sub[0] === ' ' || sub[0] === '\n') {
            pos++;
        }
        else {
            return sub;
        }
    }
    return "";
}
function coqTrimRight(s) {
    var commentDepth = 0;
    var pos = s.length - 1;
    while (pos > 0) {
        var sub = s.substring(0, pos);
        var lastChar = sub[sub.length - 1];
        if (sub.endsWith("*)")) {
            commentDepth++;
            pos -= 2;
        }
        else if (sub.endsWith("(*")) {
            commentDepth--;
            pos -= 2;
        }
        else if (commentDepth > 0) {
            pos--;
        }
        else if (lastChar === ' ' || lastChar === '\n') {
            pos--;
        }
        else {
            return sub;
        }
    }
    return "";
}
function mkAnchor(row, column, klass, insertRight) {
    var a = new Anchor(session.getDocument(), row, column);
    if (insertRight) {
        a.$insertRight = true;
    }
    a.marker = {};
    a.marker.update = function (html, markerLayer, session, config) {
        var screenPos = session.documentToScreenPosition(a);
        var height = config.lineHeight;
        var width = config.characterWidth;
        var top = markerLayer.$getTop(screenPos.row, config);
        var left = markerLayer.$padding + screenPos.column * width;
        html.push("<div class='", klass, "' style='", "height:", height, "px;", "top:", top, "px;", "left:", left, "px; width:", width, "px'></div>");
    };
    a.marker = session.addDynamicMarker(a.marker, true);
    a.on("change", function (change, anchor) {
        session._signal("changeFrontMarker");
    });
    return a;
}
function rmAnchor(a) {
    a.detach();
    session.removeMarker(a.marker.id);
}
function killAnchorsAfterPosition(pos) {
    _.remove(anchors, function (a) {
        var predicate = (a.row > pos.row || (a.row == pos.row && a.column > pos.column));
        if (predicate) {
            rmAnchor(a);
        }
        return predicate;
    });
}
function movePosRight(pos, n) {
    if (n === 0) {
        return pos;
    }
    var row = pos.row;
    var column = pos.column;
    var line = session.getLine(row);
    if (column < line.length) {
        return movePosRight({
            "row": row,
            "column": column + 1
        }, n - 1);
    }
    else if (row < session.getLength()) {
        return movePosRight({
            "row": row + 1,
            "column": 0
        }, n - 1);
    }
    else {
        return pos;
    }
}
function minPos(pos1, pos2) {
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
function capitalize(s) {
    return s.charAt(0).toUpperCase() + s.slice(1);
}
function addEditorTab(name, containerName) {
    var item = $("<li>", {
        "role": "presentation",
    }).appendTo($("#" + containerName + "-pills > ul"));
    var anchor = $("<a>", {
        "href": "#" + name + "-tab",
        "text": capitalize(name),
    })
        .appendTo(item);
    var badge = $("<span>", {
        "class": "badge",
        "id": name + "-badge",
        "html": mkGlyph("exclamation-sign"),
    })
        .css("display", "none")
        .appendTo(anchor);
    var tabPanel = $("<div>", {
        "role": "tabpanel",
        "class": "tab-pane",
        "id": name + "-tab",
    })
        .css("display", "none")
        .appendTo($("#" + containerName + "-tabs"));
    var editorDiv = $("<div>", {
        "id": name,
    })
        .appendTo(tabPanel);
    var editor = ace.edit(name);
    editor.setTheme("ace/theme/monokai");
    editor.getSession().setMode("ace/mode/ocaml");
    editor.getSession().setUseSoftTabs(true);
    editor.$blockScrolling = Infinity;
    anchor.click(function (e) {
        e.preventDefault();
        badge.css("display", "none");
        $(this).tab('show');
        $("#" + containerName + "-tabs").children(".tab-pane").css("display", "none");
        tabPanel.css("display", "flex");
        editor.resize();
        return false;
    });
    return editor;
}
