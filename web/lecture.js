
var processing = false;
var prooftree = undefined;
var nbsp = "&nbsp;";
var zwsp = "\u200B";
var namesPossiblyInScope = [];

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
            .append(nbsp + "Proof Tree")
        ,
        "id": "prooftree-button",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            syncLog("MANUALENTERPROOFTREE");
            enterProofTree();
        })
        .attr("disabled", true)
    ;

    $("<button>", {
        "class": "btn btn-danger",
        "html": $("<span>")
            .append(mkGlyph("fire"))
            .append(nbsp + "Abort Proof Tree")
        ,
        "id": "noprooftree-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
    ;

    /* Temporarily disabled
    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("cloud-download"))
            .append(nbsp + "Load remotely")
        ,
        "id": "load-remote-button",
    })
        .appendTo(buttonGroup)
        .on("click", loadRemote)
    ;

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("cloud-upload"))
            .append(nbsp + "Save remotely")
        ,
        "id": "save-remote-button",
    })
        .appendTo(buttonGroup)
        .on("click", function() { alert("TODO"); })
    ;
    */

    $("#filepicker").on("change", function() {
        // TODO: warning about resetting Coq/saving file
        loadFile();
        $(this).val(""); // forces change when same file is picked
    })

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("floppy-open"))
            .append(nbsp + nbsp + "Load")
        ,
        "id": "load-local-button",
    })
        .appendTo(buttonGroup)
        .on("click", loadLocal)
    ;

    var saveLocalButton = $("<button>", {
        "class": "btn btn-default",
        "id": "save-local-button",
    })
        .appendTo(buttonGroup)
        .on("click", saveLocal)
    ;

    $("<a>", {
        "download": "output.v",
        "id": "save-local-link",
        "html": $("<span>")
            .append(mkGlyph("floppy-save"))
            .append(nbsp + nbsp + "Save")
    })
        .css("color", "inherit")
        .css("text-decoration", "none")
        .appendTo(saveLocalButton)
    ;

    $("#main")
        .css("font-family", "monospace")
        .css("border", 0)
    ;

    $("#editor")
        .css("margin", 0)
        .css("float", "left")
        .css("width", "50%")
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

    $("body").on("keydown", globalKeyHandler);
    $("#editor").on("keydown", editorKeyHandler);
    PT.handleKeyboard();

});

function loadFile() {
    var file = $("#filepicker")[0].files[0];
    var reader = new FileReader();
    reader.onload = function(e) {
        onLoad(reader.result);
    }
    reader.readAsText(file);
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

    syncLog("LOAD " + text);

    syncResetCoqNoImports();

    $("#editor").empty().css("display", "");
    $("#coqtop").empty().css("display", "");
    $("#prooftree").empty().css("display", "none");

    $("#editor").append(
        $("<span>")
            .attr("id", "processed")
            .css("display", "inline")
            .css("padding", 0)
            .css("background-color", "#90EE90")
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "processing")
            .css("display", "inline")
            .css("padding", 0)
            .css("background-color", "#FFA500")
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "toprocess")
            .css("display", "inline")
            .css("padding", 0)
            .css("background-color", "#ADD8E6")
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "redacting")
            .css("display", "inline")
            .css("padding", 0)
            .text(zwsp + text)
    );

    highlight();

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
        .replace(/[.][a-zA-Z1-9_]/g, '__') // hides qualified identifiers
    // hide curly braces that are implicit arguments
        .replace(/\{((?:[^\.]|\.(?!\ ))*)\}/g, "_$1_")
    // make other bullets look like curly braces
        .replace(/(\.\s*)[\-\+\*](?!\))/g, "$1{")
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

function globalKeyHandler(evt) {
    if (evt.ctrlKey) {
        switch(evt.keyCode) {
        case 80: // p
            if (activeProofTree !== undefined) {
                $("#noprooftree-button").click();
            } else {
                $("#prooftree-button").click();
            }
            evt.preventDefault();
            break;
        default:
            break;
        };
    }
}

function editorKeyHandler(evt) {

    // set to false to allow default for any particular key combo
    var preventDefault = true;

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
            preventDefault = false;
            break;
        };

    } else {

        switch (evt.keyCode) {
        case 13: // Enter
            insertAtSelection("\n");
            break;
        default:
            preventDefault = false;
            break;
        };

    }

    if (preventDefault) {
        evt.preventDefault();
    }

}

var goingDown = true, goingUp = false;

function updateCoqtopPane(direction, response) {

    // some sanity check and tentative fixes
    if ($("#processing").length === 0) {
        alert("#processing is missing, attempting recovery");
        $("<span>", { "id": "processing" }).insertAfter($("#processed"));
    }
    if ($("#toprocess").length === 0) {
        alert("#toprocess is missing, attempting recovery");
        $("<span>", { "id": "toprocess" }).insertAfter($("#processing"));
    }

    var contents = response.rResponse.contents;
    switch (typeof contents) {
    case "string": break;
    case "object":
        if (contents.length > 1) {
            alert("Found contents with length greater than 1, see log");
            console.log(contents);
        }
        contents = contents[0];
        break;
    default:
        alert("Found contents with type different than string and object, see log");
        console.log(typeof contents, contents);
    };
    contents = contents.trim();

    switch (response.rResponse.tag) {
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
            if (contents !== "") {
                $("<div>", { "text": contents })
                    .css("margin-top", "10px")
                    .appendTo("#coqtop")
                ;
            }
        } else {
            $("#prooftree-button").attr("disabled", true);
            $("#coqtop").text(stripWarning(contents));
        }
        break;
    case "Fail":
        $("#coqtop")
            .toggleClass("alert-danger", true)
            .toggleClass("alert-success", false)
        ;
        // maybe still display the goal?
        //console.log("Fail", response);
        $("#coqtop").text(stripWarning(contents));
        break;
    };

    // also, enable/disable the button depending on whether we are in proof mode
    var status = syncStatus();

    // while at it, let's gather names of definitions for proof purposes
    // TODO: should this be done by prooftree.js?
    if (status.current !== null && !_(namesPossiblyInScope).contains(status.current)) {
        namesPossiblyInScope.push(status.current);
    }

    $("#prooftree-button").attr("disabled", !status.proving);
    if (status.proving) {
        // automatically enter proof mode if not in the process of proving more things
        var lastCommand = getLastProcessed();
        if (_(lastCommand).contains("(* notree *)")) {
            syncLog("NOTREE");
        }
        if (direction === goingDown
            && ! lastCommand.endsWith("Proof.")
            && !_(lastCommand).contains("(* notree *)")
            && $("#toprocess").text().length === 0) {
            syncLog("AUTOENTERPROOFTREE");
            enterProofTree();
        }
        /*
        // flash the newly-enabled button a few times
        var iterations = 3;
        var delay = 50;
        var iterate = function() {
            if (iterations-- === 0) { return; }
            $("#prooftree-button").delay(delay).fadeOut(delay).fadeIn(delay, iterate);
        }
        iterate();
        */
    }

    highlight();

}

function highlight() {
    $("#processed").html(hljs.highlight("ocaml", $("#processed").text(), true).value);
    $("#processing").html(hljs.highlight("ocaml", $("#processing").text(), true).value);
    $("#toprocess").html(hljs.highlight("ocaml", $("#toprocess").text(), true).value);
    $("#redacting").html(hljs.highlight("ocaml", $("#redacting").text(), true).value);
}

function undoCallback(response) {
    switch(response.rResponse.tag) {
    case "Good":
        var stepsToRewind = + response.rResponse.contents[0];
        console.log("Rewinding additional " + stepsToRewind + " steps");
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
    updateCoqtopPane(goingUp, response);
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
            // TODO: might be bothersome to do that at every step?
            updateCoqtopPane(goingDown, response);
            tryProcessing(); // if there is more to process
            break;
        case "Fail":
            var toprocess = $("#toprocess").text();
            var redacting = $("#redacting").text().substring(1);
            $("#toprocess").text("");
            $("#redacting").text(zwsp + pieceToProcess + toprocess + redacting);
            repositionCaret();
            updateCoqtopPane(goingDown, response);
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
    syncLog("PROVERDOWN " + pieceToProcess);
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
        syncLog("PROVERDOWN " + pieceToProcess);
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
        syncLog("PROVERUP " + pieceToUnprocess);
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
    $("#prooftree").empty();

}

function enterProofTree() {

    // this should always pass, unless we call enterProofTree manually
    var status = syncStatus();
    if (!status.proving) { return; }

    var labelBeforeProofTree = status.label;

    switchToProofUI();

    $("#noprooftree-button")
        .unbind("click")
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
    prooftree.newAlreadyStartedTheorem(
        theoremStatement,
        status.response,
        function(pt) {
            var applies = _(namesPossiblyInScope).map(function(name) {
                return "apply " + name;
            }).value();
            var leftRewrites = _(namesPossiblyInScope).map(function(name) {
                return "rewrite -> " + name;
            }).value();
            var rightRewrites = _(namesPossiblyInScope).map(function(name) {
                return "rewrite <- " + name;
            }).value();
            return applies.concat(leftRewrites, rightRewrites, PT.tDiscriminate);
        }
    );

}

function exitProofTree(labelBeforeProofTree) {

    switchToEditorUI();

    activeProofTree = undefined;

    syncLog("EXITPROOFTREE");

    // revert all the steps done in proof mode, to keep the labels clean
    var newStatus = syncStatus();

    syncRequest("rewind", newStatus.label - labelBeforeProofTree, function(){});

    repositionCaret();

}

function getLastProcessed() {
    var processed = $("#processed").text();
    return processed.substring(prev(processed)).trim();
}

function onQed(labelBeforeProofTree, prooftree) {

    var lastCommand = getLastProcessed();
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
        updateCoqtopPane(goingDown, response);
    });

    // is this enough to eventually allow garbage-collection of the proof tree?
    $("#prooftree").empty();
    activeProofTree = undefined;

    repositionCaret();

}

function stripWarning(s) {
    return s.replace(/^Warning: query commands should not be inserted in scripts\n/g, "");
}

function loadRemote() {

    var html = $("<div>");

    var files;
    syncListLectures(function(response) {
        files = response.rResponse.contents;
    });

    var fileList = $("<select>", {
        "class": "form-control",
        "id": "lecture-select",
        "width": "200px",
    }).appendTo(html);
    _(files).each(function(file) {
        fileList.append(
            $("<option>", {
                "value": file,
                "html": file,
            })
        );
    });

    $("<button>", {
        "text": "Load",
    })
        .appendTo(html)
        .on("click", function() {
            var fileToLoad = $("#lecture-select").val();
            $("#load-remote-button").popover("destroy");
            syncLoadLecture(fileToLoad, function(response) {
                onLoad(response.rResponse.contents[0]);
            });
        })
    ;

    $("<button>", {
        "text": "Cancel",
    })
        .appendTo(html)
        .on("click", function() {
            $("#load-remote-button").popover("destroy");
        })
    ;

    $("#load-remote-button")
        .popover({
            "content": html,
            "html": true,
            "placement": "bottom",
        })
        .popover("show");

}

function loadLocal() {

    $("#filepicker").click();

}

function saveLocal() {

    var text = $("#editor").text().replace(/\u200B/g, ""); // get rid of zwsp
    var blob = new Blob([text], {type:'text/plain'});
    var url = window.URL.createObjectURL(blob);
    $("#save-local-link").attr("href", url);

}

if (!String.prototype.endsWith) {
    Object.defineProperty(String.prototype, 'endsWith', {
        value: function(searchString, position) {
            var subjectString = this.toString();
            if (position === undefined || position > subjectString.length) {
                position = subjectString.length;
            }
            position -= searchString.length;
            var lastIndex = subjectString.indexOf(searchString, position);
            return lastIndex !== -1 && lastIndex === position;
        }
    });
}
