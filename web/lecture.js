
var processing = false;
var zwsp = "\u200B";

$(document).ready(function() {

    var toolBar =
        $("<div>", {
            "id": "toolbar",
        })
        .appendTo("body")
        .css("display", "table")
    ;

    var buttonGroup;

    $("<div>")
        .css("display", "table-cell")
        .css("vertical-align", "top")
        .append(
            buttonGroup = $("<div>", { "class": "btn-group" })
        )
        .appendTo(toolBar)
    ;

    var inputGroup;

    $("<div>")
        .css("display", "table-cell")
        .css("vertical-align", "top")
        .append(
            inputGroup = $("<div>", { "class": "input-group input-group-sm" })
        )
        .appendTo(toolBar)
    ;

    var inputGroup2;

    $("<div>")
        .css("display", "table-cell")
        .css("vertical-align", "top")
        .append(
            inputGroup2 = $("<div>", { "class": "input-group input-group-sm" })
        )
        .appendTo(toolBar)
    ;

    $("<input>", {
        "id": "filepicker",
        "type": "file",
    })
        .appendTo(inputGroup)
        .on("change", function() {
            // TODO: warning about resetting Coq/saving file
            loadFile();
            $(this).filestyle("clear"); // forces change when same file is picked
        })
    ;

    $("<span>", {
        "class": "input-group-addon",
        "html":
        $("<input>", {
            "checked": true,
            "type": "checkbox",
        })
            .css("vertical-align", "middle")
        ,
    })
        .appendTo(inputGroup2)
    ;

    $("<span>", { "class": "input-group-addon" })
        .text("Proof Tree")
        .css("padding-left", 0)
        .appendTo(inputGroup2)
    ;

    $("<button>", {
        "class": "btn btn-default btn-sm",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            proverDown();
        })
        .append(mkGlyph("arrow-down"))
    ;

    $("<button>", {
        "class": "btn btn-default btn-sm",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            proverUp();
        })
        .append(mkGlyph("arrow-up"))
    ;

    $(":file").filestyle({
        badge: false,
        buttonName: "btn btn-default btn-sm",
        buttonText: "&nbsp;Load a .v file",
        input: false,
    });

    $("body").append(
        $("<div>")
            .attr("id", "main")
            .addClass("panel")
            .addClass("panel-primary")
            .css("font-family", "monospace")
            .css("border", 0)
    );

    PT.resetCoqNoImports();

});

function loadFile() {
    var files = $("#filepicker")[0].files;
    if (files.length > 0) {
        var reader = new FileReader();
        reader.onload = function(e) {
            onLoad(reader.result);
        }
        reader.readAsText(files[0]);
    }
}

function resizePanes() {
    var height = $(window).height() - $("#toolbar").height();
    $("#editor").css("height", height);
    $("#coqtop").css("height", height);
}

function onLoad(text) {

    PT.resetCoqNoImports();

    var editorPane = $("<pre>")
        .attr("id", "editor")
        .attr("contenteditable", "true")
        .css("margin", 0)
        .css("float", "left")
        .css("width", "50%")
    ;

    var coqtopPane = $("<pre>")
        .attr("id", "coqtop")
        .attr("contenteditable", "false")
        .css("margin", 0)
        .addClass("alert")
        .css("float", "left")
        .css("border", 0)
        .css("width", "50%")
    ;

    $("#main").empty();
    $("#main").append(editorPane);
    $("#main").append(coqtopPane);

    resizePanes();
    $(window).resize(resizePanes);

    $("#editor").append(
        $("<span>")
            .attr("id", "processed")
            .css("background-color", "#90EE90")
            //.text(zwsp)
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "processing")
            .css("background-color", "#FFA500")
            //.text(zwsp)
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "toprocess")
            .css("background-color", "#ADD8E6")
            //.text(zwsp)
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "redacting")
            .text(zwsp + text)
    );

    $("#editor").on("keydown", keyDownHandler);

    $("#editor").focus();

}

// Some of this code has been borrowed from the ProofWeb project
// Their license is unclear, TODO make sure we can borrow, oops!

function my_index(str) {
    var delimiters = [".", "{", "}"];
    var index = +Infinity;
    _(delimiters).each(function(delimiter) {
        var pos = str.indexOf(delimiter);
        if (pos >= 0 && pos < index) { index = pos; }
    });
    if (index !== +Infinity) { return index; }
    else { return -1; }
}

function next(str) {
    return coq_find_dot(coq_undot(str), 0) + 1;
}

function prev(str) {
  return coq_find_last_dot(coq_undot(str.substring(0, str.length - 1)), 0) + 1;
}

function count (str, pat) {
    var arr = str.split (pat);
    return (arr.length);
}

// highlight dot that are terminators as opposed to the others
function coq_undot(str) {
    return str
        .replace(/[.][.][.]/g, '__.')      // emphasize the last dot of ...
        //.replace(/[.][.]/g, '__')
        .replace(/[.][a-zA-Z1-9_]/g, 'AA') // hides qualified identifiers
    ;
}

function coq_find_dot(str, toclose) {
    var index = my_index(str);
    if (index == -1) { return index; }
    var tocheck = str.substring(0, index);
    var opened = count(tocheck, "(*") + toclose - count(tocheck, "*)");
    if (opened <= 0) {
        return index;
    } else {
        var newindex = coq_find_dot(str.substring(index + 1), opened);
        if (newindex == -1) return -1;
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

function coq_find_last_dot (str, toopen) {
    var index = coq_get_last_dot(str);
    if (index == -1) { return index; }
    var tocheck = str.substring(index + 1);
    var closed = count(tocheck, "*)") + toopen - count(tocheck, "(*");
    if (closed <= 0) {
        return index;
    } else {
        var newindex = coq_find_last_dot(str.substring(0, index), closed);
        return newindex;
    }
}

function keyDownHandler(evt) {

    var prevent = true;

    if (evt.ctrlKey) {

        switch(evt.keyCode) {
        case 40: case 10: // Down
            proverDown();
            break;
        case 38: // Up
            proverUp();
            break;
        case 34: // PageDown
            break;
        case 33: // PageUp
            break;
        case 13: // Enter
            break;
        default:
            prevent = false;
            break;
        };

    } else {

        switch (evt.keyCode) {
        case 13: // Enter
            insertAtSelection("\n");
            break;
        default:
            prevent = false;
            break;
        };

    }

    if (prevent) {
        evt.preventDefault();
        evt.stopPropagation();
    }

}

function updateCoqtopPane(response) {
    switch(response.rResponse.tag) {
    case "Good":
        $("#coqtop")
            .toggleClass("alert-success", true)
            .toggleClass("alert-danger", false)
        ;
        $("#coqtop").text("");
        if (response.rGoals.focused.length > 0) {
            _(response.rGoals.focused[0].gHyps).each(function(h) {
                $("#coqtop").append(PT.showHypothesis(h) + "\n");
            });
            $("#coqtop").append($("<hr>").css("border", "1px solid black"));
            $("#coqtop").append(showTerm(response.rGoals.focused[0].gGoal));
        } else {
            $("#coqtop").append(response.rResponse.contents);
        }
        break;
    case "Fail":
        $("#coqtop")
            .toggleClass("alert-danger", true)
            .toggleClass("alert-success", false)
        ;
        // maybe still display the goal?
        $("#coqtop").text(response.rResponse.contents);
        break;
    };
    //$("#coqtop").append("\n" + JSON.stringify(response));
}

function undoCallback(response) {
    switch(response.rResponse.tag) {
    case "Good":
        var stepsToRewind = + response.rResponse.contents[0];
        while (stepsToRewind-- > 0) {
            var index = 0;
            var processed = $("#processed").text();
            var redacting = $("#redacting").text();
            if (processed != "") { index = prev(processed); }
            var pieceUnprocessed = processed.substring(index);
            $("#processed").text(processed.substring(0, index));
            $("#redacting").text(zwsp + pieceUnprocessed + redacting.substring(1));
            repositionCaret(index === 0 ? 0 : 1); // if at the start of file, no offset
            var pieceUnprocessed = processed.substring(index);
        }
        response.rResponse.contents[0] = ""; // don't show the user the steps number
        break;
    };
    updateCoqtopPane(response);
}

function tryProcessing() {
    if (processing) { return; }
    // grab the next piece to process, if any
    var toprocess = $("#toprocess").text();
    var index = next(toprocess);
    if (index === 0) { return; }
    // there is a piece to process, mark it as such
    var pieceToProcess = toprocess.substring(0, index);
    $("#processing").text(pieceToProcess);
    $("#toprocess").text(toprocess.substring(index));
    // process this piece, then process the rest
    processing = true;
    asyncQuery(pieceToProcess, function(response) {
        processing = false;
        $("#processing").text("");
        switch(response.rResponse.tag) {
        case "Good":
            $("#processed").append(pieceToProcess);
            updateCoqtopPane(response); // TODO: might be bothersome to do that at every step?
            tryProcessing(); // if there is more to process
            break;
        case "Fail":
            var redacting = $("#redacting").text().substring(1);
            $("#redacting").text(zwsp + pieceToProcess + redacting);
            repositionCaret();
            updateCoqtopPane(response);
            break;
        };
    });
}

/*
  This should simply move the next line from the #redacting area to the #toprocess area,
  then trigger a processing.
*/
function proverDown() {
    var toprocess = $("#toprocess").text();
    var redacting = $("#redacting").text();
    var index = next(redacting);
    if (index == 0) { return; }
    // 1 because we get rid of the zero-width spacing
    var pieceToProcess = redacting.substring(1, index);
    $("#toprocess").text(toprocess + pieceToProcess);
    $("#redacting").text(zwsp + redacting.substring(index));
    repositionCaret();
    tryProcessing();
}

/*
  Assuming the system is done processing, #processing and #toprocess should be empty, we
  should therefore be able to just undo the last step. Undo might undo more steps than
  that though, in which case we want to mark them undone too.
*/
function proverUp () {
    if (processing) { return; } // TODO: could prevent more processing?
    var index = 0;
    var processed = $("#processed").text();
    var redacting = $("#redacting").text();
    if (processed != "") { index = prev(processed); }
    var pieceToUnprocess = processed.substring(index);
    if (pieceToUnprocess !== "") {
        $("#processed").text(processed.substring(0, index));
        $("#redacting").text(zwsp + pieceToUnprocess + redacting.substring(1));
        repositionCaret(index === 0 ? 0 : 1); // if at the start of file, no offset
        syncUndo(undoCallback);
    }
}

// moves the caret to the start of the #redacting area
// [offset] allows to move it slightly more
function repositionCaret(offset) {
    if (offset === undefined) { offset = 0; }
    var sel = rangy.getSelection();
    var rng = rangy.createRange();
    // 1 for the zwsp
    rng.setStart($("#redacting").contents()[0], 1 + offset);
    sel.setSingleRange(rng);

    // now let's scroll so that the cursor is visible
    var cursorMargin = 40; // about two lines
    var cursorTop = $("#redacting")[0].getBoundingClientRect().top;
    var editorRect = $("#editor")[0].getBoundingClientRect();
    var editorBottom = editorRect.bottom;
    var editorTop = editorRect.top;
    var editorScroll = $("#editor").scrollTop();

    // scroll down if the cursor is too far
    if (cursorTop > editorBottom - cursorMargin) {
        $("#editor").scrollTop(editorScroll + cursorTop - editorBottom + cursorMargin);
    }

    // scroll up if the cursor is too far
    if (cursorTop < editorTop + cursorMargin) {
        // avoid scrolling at the bottom when at the top
        var scroll = Math.max(0, editorScroll + cursorTop - editorTop - cursorMargin);
        $("#editor").scrollTop(scroll);
    }

}

function syncRequest(r, q, h) {
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: false,
        success: function(response) {
            h(response);
        }
    });
}
function syncQuery(q, h) { syncRequest('query', q, h); }
function syncQueryAndUndo(q, h) { syncRequest('queryundo', q, h); }
function syncUndo(h) { syncRequest('undo', undefined, h); }

function asyncRequest(r, q, h) {
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: r,
        data: {query : q},
        async: true,
        success: function(response) {
            h(response);
        }
    });
}
function asyncQuery(q, h) { asyncRequest('query', q, h); }
function asyncQueryAndUndo(q, h) { asyncRequest('queryundo', q, h); }
function asyncUndo(h) { asyncRequest('undo', undefined, h); }

function mkGlyph(name) {
    return $("<i>", {
        "class": "glyphicon glyphicon-" + name,
    });
}

function insertAtSelection(txt) {
    var sel, newrange;
    sel = rangy.getSelection();
    if (sel.rangeCount > 0) {
        newrange = insertText(txt,sel.getRangeAt(0));
        sel.setSingleRange(newrange);
    }
}

function insertText(txt,inrange) {
    var range = inrange.cloneRange();
    var tn = document.createTextNode(txt);
    range.insertNode(tn);
    range.selectNode(tn);
    range.normalizeBoundaries();
    range.collapse(false);
    return range;
}
