
var processing = false;
var prooftree = undefined;
var zwsp = "\u200B";

var delimiters = [".", "{", "}"];

var unicodeList = [
    ("forall", "∀"),
    ("\/", "∨"),
    ("/\\", "∧"),
    ("neg", "¬"),
];

$(document).ready(function() {

    var toolBar =
        $("#toolbar")
        .css("display", "table")
        .css("border", 0)
        .css("margin", 0)
        .css("padding", 0)
    ;

    var buttonGroup =
        $(".btn-group")
        .css("display", "table-cell")
        .css("vertical-align", "top")
    ;

    var inputGroup =
        $(".input-group")
        .css("display", "table-cell")
        .css("vertical-align", "top")
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

    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-down",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            proverDown();
        })
        .append(mkGlyph("arrow-down"))
    ;

    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-up",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            proverUp();
        })
        .append(mkGlyph("arrow-up"))
    ;

    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-caret",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            proverToCaret();
        })
        .append(mkGlyph("arrow-right"))
        .append(mkGlyph("italic"))
    ;

    $("<button>", {
        "class": "btn btn-success",
        "html": $("<span>")
            .append(mkGlyph("tree-deciduous"))
            .append(nbsp + "Proof Tree" + nbsp)
        ,
        "id": "prooftree-button",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            enterProofTree();
        })
        .attr("disabled", true)
    ;

    $("<button>", {
        "class": "btn btn-danger",
        "html": $("<span>")
            .append(mkGlyph("fire"))
            .append(nbsp + "Abort Proof Tree" + nbsp)
        ,
        "id": "noprooftree-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
    ;

    $(":file").filestyle({
        badge: false,
        buttonName: "btn btn-default",
        buttonText: nbsp + "Load a .v file",
        input: false,
    });

    $("#main")
        .css("font-family", "monospace")
        .css("border", 0)
    ;

    $("#editor")
        .css("margin", 0)
        .css("float", "left")
        .css("width", "50%")
        .on("keydown", keyDownHandler);
    ;

    $("#coqtop")
        .css("margin", 0)
        .css("float", "left")
        .css("width", "50%")
        .css("border", 0)
    ;

    $("#prooftree")
        .css("border", 0)
        .css("display", "none")
    ;

    resize();
    $(window).resize(resize);

    syncResetCoqNoImports();
    PT.handleKeyboard();

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

function resize() {
    var windowHeight = $(window).height();
    // careful, there are many <body> when using proof tree!
    $("html > body").height(windowHeight);
    var height = windowHeight - $("#toolbar").height();
    $("#editor").css("height", height);
    $("#coqtop").css("height", height);
    $("#prooftree").css("height", height);
    $("#pt-1").css("height", height);
    $("svg").css("height", height);
    // TODO: fix height bug
    var width = $(window).width();
    if (prooftree !== undefined) { prooftree.resize($(window).width(), height); }
}

function onLoad(text) {

    syncResetCoqNoImports();

    $("#editor").empty().css("display", "");
    $("#coqtop").empty().css("display", "");
    $("#prooftree").empty().css("display", "none");

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

    $("#editor").focus();

}

// Some of this code has been borrowed from the ProofWeb project
// Their license is unclear, TODO make sure we can borrow, oops!

function my_index(str) {
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
    // hide curly braces that are implicit arguments
        .replace(/\{((?:[^\.]|\.(?!\ ))*)\}/g, "_$1_")
    // make other bullets look like curly braces
        .replace(/(\.\s*)[\-\+\*]/g, "$1{")
        .replace(/^([\u200B\s]*)[\-\+\*]/, "$1{")
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
            proverToCaret();
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
            $("#prooftree-button").attr("disabled", true);
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

    // also, enable/disable the button depending on whether we are in proof mode
    var status = syncStatus();
    $("#prooftree-button").attr("disabled", !status.proving);
    if (status.proving) {
        var iterations = 3;
        var delay = 50;
        var iterate = function() {
            if (iterations-- === 0) { return; }
            $("#prooftree-button").delay(delay).fadeOut(delay).fadeIn(delay, iterate);
        }
        iterate();
    }
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
  Returns the position of the caret w.r.t. the editor: this includes all the characters in
  #processed, #processing, #toprocess and #redacting
*/
function getCaretPos() {
    var sel = rangy.getSelection();
    var rng = rangy.createRange();
    rng.selectNodeContents($("#editor").get(0));
    rng.setEnd(sel.focusNode,sel.focusOffset);
    return rng.toString().length;
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

function proverToCaret () {
    if (processing) { return; }
    var index = getCaretPos();
    var processed = $("#processed").text();
    var processing = $("#processing").text();
    var toprocess = $("#toprocess").text();
    var redacting = $("#redacting").text();
    // the caret is in the processed region, undo actions
    if (index < processed.length) {
        var caretInitialPosition = getCaretPos();
        // this assumes proverUp is synchronous
        while ($("#processed").text().length > caretInitialPosition) {
            proverUp();
        }
    } else {
        index -= processed.length + processing.length + toprocess.length;
        // if the caret is in the #processing or #toprocess, do nothing
        if (index <= 0) { return; }
        // if the character at index is not a delimiter, process to the next one
        if (!_(delimiters).contains(redacting[index-1])) {
            index += next(redacting.substring(index));
        }
        var pieceToProcess = redacting.substring(1, index); // 1 for zwsp
        $("#toprocess").text(toprocess + pieceToProcess);
        $("#redacting").text(zwsp + redacting.substring(index));
        repositionCaret();
        tryProcessing();
    }
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

function switchToProofUI() {

    $("#editor").css("display", "none");
    $("#coqtop").css("display", "none");
    $("#prooftree").css("display", "");
    $("#prover-down").attr("disabled", true);
    $("#prover-up").attr("disabled", true);
    $("#prover-caret").attr("disabled", true);
    $("#prooftree-button").css("display", "none");
    $("#noprooftree-button").css("display", "");

}

function switchToEditorUI() {

    $("#editor").css("display", "");
    $("#coqtop").css("display", "");
    $("#prooftree").css("display", "none");
    $("#prover-down").attr("disabled", false);
    $("#prover-up").attr("disabled", false);
    $("#prover-caret").attr("disabled", false);
    $("#prooftree-button").css("display", "");
    $("#noprooftree-button").css("display", "none");

}

function enterProofTree() {

    // this should always pass, unless we call enterProofTree manually
    var status = syncStatus();
    if (!status.proving) { return; }

    var labelBeforeProofTree = status.label;

    switchToProofUI();

    $("#noprooftree-button")
        .on("click", function() { exitProofTree(labelBeforeProofTree); })
    ;

    prooftree = new ProofTree(
        $("#prooftree")[0],
        $(window).width(),
        $(window).height() - $("#toolbar").height(),
        _.partial(onQed, labelBeforeProofTree)
    );

    /*
      need to figure out what the statement of the theorem is, and there seems to be no way to
      ask that with status, so look it up in the processed region as the last statement
    */
    var processed = $("#processed").text();
    var assertionKeywords = [
        "Theorem", "Lemma", "Remark", "Fact", "Corollary", "Proposition"
    ];
    // lookup the last time an assertion keyword was processed
    var position = _(assertionKeywords)
        .map(function(keyword) {
            return processed.lastIndexOf(keyword);
        })
        .max()
        .value()
    ;
    var theoremStatement = processed.substring(position);
    // get rid of anything after the statement, like "Proof."
    theoremStatement = theoremStatement.substring(0, next(theoremStatement));
    prooftree.newAlreadyStartedTheorem(theoremStatement, status.response);

}

function exitProofTree(labelBeforeProofTree) {

    switchToEditorUI();

    // revert all the steps done in proof mode, to keep the labels clean
    var newStatus = syncStatus();
    syncRequest("rewind", newStatus.label - labelBeforeProofTree, function(){});

    repositionCaret();

}

function onQed(labelBeforeProofTree, prooftree) {

    var processed = $("#processed").text();
    var lastCommand = processed.substring(prev(processed)).trim();

    var textToAppend = (lastCommand === "Proof.") ? "\n" : "\nProof.\n";
    var proof = PT.pprint(prooftree.proof(), 1, " ", "\n");
    textToAppend += proof;
    textToAppend += "\nQed."; // invariant: #processed ends on a period
    $("#processed").append(textToAppend);

    switchToEditorUI();

    // first, revert all the steps done in proof mode, to keep the labels clean
    var newStatus = syncStatus();
    syncRequest("rewind", newStatus.label - labelBeforeProofTree, function(){});
    // since we are going to write Proof., we must actually send it
    if (lastCommand !== "Proof.") {
        syncQuery("Proof.", function(){});
    }
    // now we can replay the actuall proof and conclude
    prooftree.replay();
    syncQuery("Qed.", function(response) {
        updateCoqtopPane(response);
    });

    // is this enough to eventually allow garbage-collection of the proof tree?
    $("#prooftree").empty();
    activeProofTree = undefined;

    repositionCaret();

}
