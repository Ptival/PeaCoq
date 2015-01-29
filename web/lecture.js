var highlightingDelay = 1000; // milliseconds

var processing = false;
var prooftree = undefined;
var nbsp = "\u00A0";
var zwsp = "\u200B";
var namesPossiblyInScope = [];

var electric = false;
var workaround_no_focusing = false;

var proved = "";
var proving = "";
var provwill = "";

var delimiters = [".", "{", "}"];

var unicodeList = [
    ("forall", "∀"),
    ("\/", "∨"),
    ("/\\", "∧"),
    ("neg", "¬"),
];

$(document).ready(function() {

    $(window).bind('beforeunload', function(){
        return '⚠⚠⚠ unsaved progress wil be lost ⚠⚠⚠';
    });

    if (!rangy.initialized) {rangy.init();}

    hljs.configure({'languages': ['ocaml']});

    // Range.textContent : String.
    // Returns the data content of all text nodes in the range, ignoring visibility.
    rangy.rangePrototype.textContent = function() {
        var textnodes = this.getNodes([3]);
        var tn, res="";

        for (var i=0; i < textnodes.length; i++) {
            tn = textnodes[i];
            if (tn === this.startContainer && tn === this.endContainer) {
                res += tn.data.slice(this.startOffset, this.endOffset);
            }
            else if (tn === this.startContainer) {
                res += tn.data.slice(this.startOffset);
            }
            else if (tn === this.endContainer) {
                res += tn.data.slice(0,this.endOffset);
            }
            else {
                res += tn.data;
            }
        }

        return res;
    }

    var buttonGroup = $(".btn-group");

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
            //.append(nbsp + "Proof Tree")
        ,
        "id": "prooftree-button",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            asyncLog("MANUALENTERPROOFTREE");
            enterProofTree();
        })
        .attr("disabled", true)
    ;

    $("<button>", {
        "class": "btn btn-danger",
        "html": $("<span>")
            .append(mkGlyph("fire"))
            //.append(nbsp + "Abort Proof Tree")
        ,
        "id": "noprooftree-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
    ;

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("eye-open"))
            //.append(nbsp + "Peek at Editor")
        ,
        "id": "peek-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
        .on("click", peekAtEditorUI)
    ;

    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("eye-close"))
            //.append(nbsp + "Return to Proof Tree")
        ,
        "id": "unpeek-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
        .on("click", unpeekAtEditorUI)
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
        "html": $("<span>")
            .append(mkGlyph("floppy-save"))
            .append(nbsp + nbsp + "Save"),
    })
        .appendTo(buttonGroup)
        .on("click", saveLocal)
    ;

    $("<button>", {
        "class": "btn btn-info",
        "data-target": "feedback",
        "data-toggle": "modal",
        "id": "feedback-button",
        "html": $("<span>")
            .append(mkGlyph("bullhorn"))
            //.append(nbsp + nbsp + "Feedback"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            $("#feedback").modal();
        })
    ;

    $("#feedback").on('shown.bs.modal', function () {
        $("#feedback-form").focus();
    });

    $("#submit-feedback").on("click", function() {
        var feedback = $("#feedback-form").text();
        $("#feedback-form").text("");
        asyncLog("FEEDBACK " + feedback);
        $("#cancel-feedback").click();
    });

    $("<button>", {
        "class": "btn btn-default",
        "data-target": "help",
        "data-toggle": "modal",
        "id": "feedback-button",
        "html": $("<span>")
            .append(mkGlyph("question-sign"))
            //.append(nbsp + nbsp + "Help"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            $("#help").modal();
        })
    ;

    $("<button>", {
        "class": "btn btn-default",
        "html": '<img src="media/ajax-loader.gif" />',
        "id": "loading",
    })
        .appendTo(buttonGroup)
        .css("padding", "2px 10px")
        .css("display", "none")
    ;

    $("<a>", {
        "download": "output.v",
        "id": "save-local-link",
    })
        .css("display", "none")
        .appendTo(buttonGroup)
    ;

    resetEditorWith("(* Your code here *)");

    resize();
    $(window).resize(resize);

    $("body")
        .on("keydown", globalKeyHandler)
    ;

    $("#editor")
        .keypress(keypressHandler)
        .keydown(keydownHandler)
        .on("cut", pweCutHandler)
        .on("paste", pwePasteHandler)
    ;

    //PT.handleKeyboard();

    asyncRevision()
        .then(function(response) {
            $("#revision").html(
                "Server revision: " + response.rResponse.contents[0]
                    + "<br/>Client revision: " + response.rResponse.contents[1]
            );
            return asyncResetCoq();
        })
        .then(function() {
            $("#editor").focus();
        })
        .catch(outputError)
    ;

});

function loadFile() {
    var file = $("#filepicker")[0].files[0];
    $("#save-local-link").attr(
        "download",
        // remove versioning number
        file.name.replace(/ \(\d+\)/g, '')
    );
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

    text = pweSanitizeInput(text);

    asyncLog("LOAD " + text);

    $("#editor").empty().css("display", "");
    $("#coqtop").empty().css("display", "");
    $("#prooftree").empty().css("display", "none");

    resetEditorWith(text);

    switchToEditorUI();

    highlight();

    asyncResetCoq()
        .then(function() {
            $("#editor").focus();
        })
        .catch(outputError);

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
        .replace(/\{((?:[^\.\}]|\.(?!\ ))*)\}/g, "_$1_")
    // make other bullets look like curly braces
        .replace(/(\.\s*)[\-\+\*](?!\))/g, "$1{")
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
    if (evt.ctrlKey && evt.altKey) {
        switch(evt.keyCode) {
        case 84: // t
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

function keypressHandler(ev) {
    //console.log("KEYPRESS", ev.keyCode)
    pweRestoreFinalBR();
    pweOptAdjustSelection();
    if (!(ev.keyCode >= 33 && ev.keyCode <= 40) && pweSelectionLocked()) {
        ev.preventDefault();
        ev.stopPropagation();
    }
}

function keyupHandler(evt) {
    var bufferText = $("#buffer").text();
    if (bufferText === zwsp) { return; }
    var unlocked = $("#unlocked").text();
    $("#buffer").text(zwsp);
    $("#unlocked").text(bufferText.substring(1) + unlocked);
}

function keydownHandler(ev) {

    eventuallyHighlight();

    pweRestoreFinalBR();
    pweOptAdjustSelection();

    //console.log("KEYDOWN", ev.keyCode)

    // Ctrl+C is copy
    // Ctrl+A/B/E/F/N/P move the cursor under Mac
    var ctrlWhitelist = [
        65, // a
        66, // b
        67, // c
        69, // e
        70, // f
        78, // n
        80, // p
    ];

    // Meta+C is copy under Mac
    if (ev.metaKey && evt.keyCode === 67) {
        return;
    }

    if (ev.ctrlKey) {
        if (ev.keyCode == 40 || ev.keyCode == 10) { //DOWN_ARROW
            proverDown();
            ev.preventDefault();
            ev.stopPropagation();
        } else if (ev.keyCode == 38) { // Up
            proverUp();
            ev.preventDefault();
            ev.stopPropagation();
        } else if (ev.keyCode == 34) { // PgDn
            //prover_bottom();
            ev.preventDefault();
            ev.stopPropagation();
        } else if (ev.keyCode == 33) { // PgUp
            //prover_top();
            ev.preventDefault();
            ev.stopPropagation();
        } else if (ev.keyCode == 13) { // Enter
            proverToCaret();
            ev.preventDefault();
            ev.stopPropagation();
        } else if (ev.keyCode == 8) { // Backspace
            // tricky, for now just backspace
            pweEmulateBackspace(ev, true);
        } else if (
            !pweSelectionLocked()
                || _(ctrlWhitelist).contains(ev.keyCode)) {
            // in the locked area, only whitelisted commands are allowed
            return;
        } else { // selection is locked and command is not whitelisted
            ev.preventDefault();
            ev.stopPropagation();
        }
    }

    if (electric==true && evt.keyCode == 190) { setTimeout(proverToCaret, 0); }

    if (ev.keyCode >= 33 && ev.keyCode <= 40) {
        if (ev.keyCode == 37) { // Left
            if (pweMoveLeft(ev.shiftKey)) {
                ev.preventDefault();
                ev.stopPropagation();
            }
        }
        if (ev.keyCode == 39) { // Right
            if (pweMoveRight(ev.shiftKey)) {
                ev.preventDefault();
                ev.stopPropagation();
            }
        }
    } else if (!pweSelectionLocked()) {
        if (ev.keyCode == 8) { // Backspace
            pweEmulateBackspace(ev, false);
        } else if (ev.keyCode == 9) { // Tab
            insertAtSelection("  ");
            ev.preventDefault();
            ev.stopPropagation();
        } else if (ev.keyCode == 13 && !ev.ctrlKey) { // Enter
            // there is no way around emulating this: the browser adds a new <div>...
            pweEmulateReturn();
            ev.preventDefault();
            ev.stopPropagation();
        }
    } else {
        ev.preventDefault();
        ev.stopPropagation();
    }

}

var lastHighlight = Date.now();

function eventuallyHighlight() {
    lastHighlight = Date.now();
    window.setTimeout(function() {
        var now = Date.now();
        var delta = now - lastHighlight;
        if (delta > highlightingDelay) {
            highlight();
        }
    }, highlightingDelay);
}

var goingDown = true, goingUp = false;

function updateCoqtopPane(direction, response) {

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

        var nbFocused = response.rGoals.focused.length;
        var unfocused = response.rGoals.unfocused[0];

        if (nbFocused > 0) {
            _(response.rGoals.focused[0].gHyps).each(function(h) {
                $("#coqtop").append(PT.showHypothesis(extractHypothesis(h)) + "\n");
            });
            $("#coqtop").append($("<hr>").css("border", "1px solid black"));
            $("#coqtop").append(showTerm(extractGoal(response.rGoals.focused[0].gGoal)));

            var goalsDiv = $("<div>")
                .css("margin-top", "10px")
                .appendTo("#coqtop")
            ;
            var nbUnfocused = (unfocused === undefined)
                ? 0
                : unfocused[0].length + unfocused[1].length
            ;
            if (nbUnfocused === 0) {
                goalsDiv.text(
                    nbFocused + " subgoal" + (nbFocused <= 1 ? "" : "s")
                );
            } else {
                goalsDiv.text(
                    nbFocused + " focused subgoal" + (nbFocused <= 1 ? "" : "s")
                        + ", " + nbUnfocused + " unfocused"
                );
            }

            if (contents !== "") {
                $("<div>", { "text": contents })
                    .css("margin-top", "10px")
                    .appendTo("#coqtop")
                ;
            }

        } else if (unfocused !== undefined) {

            var nbRemaining = unfocused[0].length + unfocused[1].length;

            var goalsDiv = $("<div>", {
                "text": nbRemaining + " remaining subgoal" + (nbRemaining <= 1 ? "" : "s")
            })
                .css("margin-top", "10px")
                .appendTo("#coqtop")
            ;

        } else {

            $("#prooftree-button").attr("disabled", true);

            contents = stripWarning(contents);

            // postprocessing of Inductive
            if (contents.startsWith("Inductive")) {
                contents = contents
                    .replace(/:=\s+/, ":=\n| ")
                    .replace(/ \| /, "\n| ")
                ;
            }

            $("#coqtop").html(contents);

        }

        // if we use highlightBlock here, it fails, so use the core highlighting
        var coqtopText = $("#coqtop").text();
        var textHl = hljs.highlight('ocaml', coqtopText, true).value;
        $("#coqtop").html(textHl);

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
    asyncStatus()
        .then(function(status) {

            // while at it, let's gather names of definitions for proof purposes
            // TODO: should this be done by prooftree.js?
            if (status.current !== null && !_(namesPossiblyInScope).contains(status.current)) {
                namesPossiblyInScope.push(status.current);
            }

            $("#prooftree-button").attr("disabled", !status.proving);
            if (status.proving) {
                // automatically enter proof mode if not in the process of proving more things
                var lastCommand = getLastProved();
                if (_(lastCommand).contains("(* notree *)")) {
                    asyncLog("NOTREE");
                }
                if (direction === goingDown
                    && ! lastCommand.endsWith("Proof.")
                    && !_(lastCommand).contains("(* notree *)")
                    && $("#provwill").text().length === 0) {
                    if (!processing) {
                        asyncLog("AUTOENTERPROOFTREE");
                        enterProofTree();
                    }
                }
            }

        })
    ;

}

function highlight() {
    var sel = rangy.saveSelection();
    // need to undo previous highlightings because hljs is dumb
    var hljsClasses = [
        "built_in",
        "comment",
        "keyword",
        "literal",
        "number",
        "params",
        "string",
        "title",
        "type",
    ];
    _(hljsClasses).each(function(className) {
        $("#editor .hljs-" + className).replaceWith(function() { return this.innerHTML; });
    });
    hljs.highlightBlock($("#editor")[0]);
    $("#editor").removeClass("hljs"); // no thanks
    rangy.restoreSelection(sel);
}

function undoCallback(response) {
    switch(response.rResponse.tag) {
    case "Good":
        var stepsToRewind = + response.rResponse.contents[0];
        //console.log("Rewinding additional " + stepsToRewind + " steps");
        while (stepsToRewind-- > 0) {
            var index = 0;
            var unlocked = pweGetUnlocked();
            if (proved != "") { index = prev(proved); }
            var pieceUnproved = proved.substring(index);
            proved = proved.substring(0, index);
            pweSetLockedPart("proved", proved);
            pweSetUnlocked(pieceUnproved + unlocked);
        }
        repositionCaret();
        response.rResponse.contents[0] = ""; // don't show the user the steps number
        break;
    };
    updateCoqtopPane(goingUp, response);
}

function tryProcessing(callback) {

    if (processing) { return; }

    // grab the next piece to process, if any
    var index = next(provwill);
    if (index === 0) {
        highlight();
        if (callback !== undefined) {
            callback();
        }
        return;
    }
    // there is a piece to process, mark it as such
    proving = provwill.substring(0, index);
    provwill = provwill.substring(index);

    pweSetLockedPart("provwill", provwill);
    pweSetLockedPart("proving", proving);
    //highlight();

    // sometimes, a leftover \n stays in the #provwill area, remove it
    /*
    if($("#provwill").text().trim === "") {
        $("#provwill").text("");
    }
    */
    asyncLog("PROVERDOWN " + proving);
    // process this piece, then process the rest
    processing = true;
    asyncQuery(proving).then(function(response) {
        processing = false;
        switch(response.rResponse.tag) {
        case "Good":
            proved = proved + proving;
            proving = "";
            pweSetLockedPart("proved", proved);
            pweSetLockedPart("proving", proving);
            // TODO: might be bothersome to do that at every step?
            updateCoqtopPane(goingDown, response);
            //repositionCaret();
            tryProcessing(callback); // if there is more to process
            break;
        case "Fail":
            var unlocked = pweGetUnlocked();
            pweSetUnlocked(proving + provwill + unlocked);
            proving = "";
            pweSetLockedPart("proving", proving);
            provwill = "";
            pweSetLockedPart("provwill", provwill);
            repositionCaret();
            updateCoqtopPane(goingDown, response);
            break;
        };
    });

}

/*
  Returns the position of the caret w.r.t. the editor: this includes all the
  characters in #proved, #proving, #provwill and #unlocked
*/
function getCaretPos() {
    var sel = rangy.getSelection();
    var rng = rangy.createRange();
    rng.selectNodeContents($("#editor")[0]);
    rng.setEnd(sel.focusNode, sel.focusOffset);
    return rng.toString().length;
}

/*
  This should simply move the next line from the #unlocked area to the #provwill
  area, then trigger a processing.
*/
function proverDown() {
    var unlocked = pweGetUnlocked();
    var index = next(unlocked);
    if (index == 0) { return; }
    var pieceToProcess = unlocked.substring(0, index);
    unlocked = unlocked.substring(index);
    // if there is no spacing before the command to be inserted, add one!
    var stringBefore = proved + proving + provwill;
    if (stringBefore !== '') {
        var characterBefore = stringBefore[stringBefore.length - 1];
        var characterAfter = pieceToProcess[0];
        if (characterBefore !== ' ' && characterBefore !== '\n'
            && characterAfter !== ' ' && characterAfter !== '\n') {
            provwill += ' ';
        }
    }
    provwill += pieceToProcess;
    pweSetLockedPart("provwill", provwill);
    pweSetUnlocked(unlocked);
    tryProcessing(repositionCaret);
}

function proverRewindToIndex(index) {
    if (proved.length > index) {
        return proverUp().then(function() { return proverRewindToIndex(index); });
    } else {
        return Promise.resolve();
    }
}

function proverToCaret () {
    if (processing) { return; }
    var index = getCaretPos();
    //var proved = $("#proved").text();
    //var processing = $("#proving").text();
    //var provwill = $("#provwill").text();
    var unlocked = pweGetUnlocked();
    // the caret is in the proved region, undo actions
    if (index < proved.length) {
        proverRewindToIndex(index);
    } else {
        index -= proved.length + proving.length + provwill.length + 1;
        // if the caret is in the #proving or #provwill, do nothing
        if (index <= 0) { return; }
        // if the character at index is not a delimiter, process to the next one
        if (!_(delimiters).contains(unlocked[index-1])) {
            index += next(unlocked.substring(index));
        }
        var pieceToProcess = unlocked.substring(0, index);
        provwill = provwill + pieceToProcess;
        pweSetLockedPart("provwill", provwill);
        pweSetUnlocked(unlocked.substring(index));
        asyncLog("PROVERDOWN " + pieceToProcess);
        repositionCaret();
        tryProcessing();
    }
}

/*
  Assuming the system is done processing, #proving and #provwill should be
  empty, we should therefore be able to just undo the last step. Undo might undo
  more steps than that though, in which case we want to mark them undone too.
*/
function proverUp () {
    if (processing) { return; } // TODO: could prevent more processing?
    var index = 0;
    var unlocked = pweGetUnlocked();
    if (proved != "") { index = prev(proved); }
    var pieceToUnprocess = proved.substring(index);
    if (pieceToUnprocess !== "") {
        proved = proved.substring(0, index);
        pweSetLockedPart("proved", proved);
        pweSetUnlocked(pieceToUnprocess + unlocked);
        asyncLog("PROVERUP " + pieceToUnprocess);
        repositionCaret();
        return asyncUndo()
            .then(undoCallback)
        ;
    } else {
        return Promise.resolve();
    }
}

// moves the caret to the start of the #unlocked area
// [offset] allows to move it slightly more
function repositionCaret(offset) {
    if (offset === undefined) { offset = 0; }
    var sel = rangy.getSelection();
    var rng = rangy.createRange();
    var contents = $("#unlocked").contents();
    rng.setStart(
        (contents.length === 0) ? $("#unlocked")[0] : contents[0],
        offset
    );
    sel.setSingleRange(rng);

    scrollViewToCaret();

}

function scrollViewToCaret() {
    // now let's scroll so that the cursor is visible
    var cursorMargin = 40; // about two lines
    var cursorTop = getCaretVerticalPosition();
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
        newrange = insertText(txt, sel.getRangeAt(0));
        sel.setSingleRange(newrange);
    }
}

function insertText(txt, inrange) {
    var range = inrange.cloneRange();
    var tn = document.createTextNode(txt);
    range.insertNode(tn);
    range.selectNode(tn);
    range.normalizeBoundaries();
    range.collapse(false);
    return range;
}

function getCaretVerticalPosition() {
    var sel = rangy.getSelection();
    var range = sel.getRangeAt(0).cloneRange();
    var span = $("<span>", { "id": "toremove", "text": " " })[0];
    range.insertNode(span);
    var caretTop = span.getBoundingClientRect().top;
    span.remove();
    return caretTop;
}

function peekAtEditorUI() {

    $("#editor").css("display", "");
    $("#coqtop").css("display", "");
    $("#prooftree").css("display", "none");
    $("#peek-button").css("display", "none");
    $("#unpeek-button").css("display", "");
    $("#editor").focus();

}

function unpeekAtEditorUI() {

    $("#editor").css("display", "none");
    $("#coqtop").css("display", "none");
    $("#prooftree").css("display", "");
    $("#peek-button").css("display", "");
    $("#unpeek-button").css("display", "none");
    $("#prooftree").focus();

}

function switchToProofUI() {

    $("#editor").css("display", "none");
    $("#coqtop").css("display", "none").text("CURRENTLY IN PROOF TREE MODE");
    $("#prooftree").css("display", "");
    $("#prover-down").attr("disabled", true);
    $("#prover-up").attr("disabled", true);
    $("#prover-caret").attr("disabled", true);
    $("#prooftree-button").css("display", "none");
    $("#noprooftree-button").css("display", "");
    $("#peek-button").css("display", "");
    $("#editor").attr("contenteditable", false);

}

function switchToEditorUI() {

    $("#editor").css("display", "");
    $("#coqtop").css("display", "").text("");
    $("#prooftree").css("display", "none");
    $("#prover-down").attr("disabled", false);
    $("#prover-up").attr("disabled", false);
    $("#prover-caret").attr("disabled", false);
    $("#prooftree-button").css("display", "");
    $("#noprooftree-button").css("display", "none");
    $("#peek-button").css("display", "none");
    $("#unpeek-button").css("display", "none");
    $("#editor").attr("contenteditable", true);

}

function enterProofTree() {

    // do this as early as possible to avoid races
    switchToProofUI();

    asyncStatus()
        .then(function(status) {

            var labelBeforeProofTree = status.label;

            $("#noprooftree-button")
                .unbind("click")
                .on("click", function() { exitProofTree(labelBeforeProofTree); })
            ;

            prooftree = new ProofTree(
                $("#prooftree")[0],
                $(window).width(),
                $(window).height() - $("#toolbar").height(),
                _.partial(onQed, labelBeforeProofTree),
                function() { $("#loading").css("display", ""); },
                function() { $("#loading").css("display", "none"); }
            );

            /*
              need to figure out what the statement of the theorem is, and
              there seems to be no way to ask that with status, so look it up in
              the proved region as the last statement
            */
            var proved = $("#proved").text();
            var assertionKeywords = [
                "Theorem", "Lemma", "Remark", "Fact", "Corollary", "Proposition"
            ];
            // lookup the last time an assertion keyword was proved
            var position = _(assertionKeywords)
                .map(function(keyword) {
                    return proved.lastIndexOf(keyword);
                })
                .max()
                .value()
            ;
            var theoremStatement = proved.substring(position);
            // get rid of anything after the statement, like "Proof."
            theoremStatement = theoremStatement.substring(0, next(theoremStatement));
            prooftree.newAlreadyStartedTheorem(
                theoremStatement,
                status.response,
                lectureTactics
            );

        })
        .catch(outputError);
    ;

}

function exitProofTree(labelBeforeProofTree) {

    switchToEditorUI();

    var pt = activeProofTree;
    var partialProof = pt.partialProofFrom(pt.rootNode, 1);
    // post-process so that text looks rad
    partialProof.find("div").prepend("\n");
    partialProof.find("textarea").replaceWith("admit.");
    partialProof.find("button").remove();

    // make sure there is a character to go right of
    var unlocked = pweGetUnlocked();
    if (unlocked === "") { pweSetUnlocked("\n"); }
    repositionCaret();
    pweMoveRight(); // so that we are past the zwsp

    var partialProofText = pweSanitizeInput(partialProof.text());
    // if the partial proof has anything interesting, save it in a comment
    if (partialProofText !== "admit.") {
        insertAtSelection(
            "(*\n"
                + partialProofText
                + "\n*)\n"
        );
    }

    $("#prooftree").empty();
    activeProofTree = undefined;

    asyncLog("EXITPROOFTREE");

    // revert all the steps done in proof mode, to keep the labels clean
    asyncStatus()
        .then(function(newStatus) {
            return asyncRequest(
                "rewind",
                newStatus.label - labelBeforeProofTree
            );
        })
    ;

}

function getLastProved() {
    var proved = $("#proved").text();
    return proved.substring(prev(proved)).trim();
}

function onQed(labelBeforeProofTree, prooftree) {

    var lastCommand = getLastProved();
    var textToAppend = (lastCommand === "Proof.") ? "\n" : "\nProof.\n";
    var proof = PT.pprint(prooftree.proof(), 1, " ", "\n");
    textToAppend += proof;
    textToAppend += "\nQed."; // invariant: #proved ends on a period
    proved += textToAppend;
    pweSetLockedPart("proved", proved);

    switchToEditorUI();

    // first, revert all the steps done in proof mode, to keep the labels clean
    asyncStatus()
        .then(function(newStatus) {
            return asyncRequest(
                "rewind",
                newStatus.label - labelBeforeProofTree
            );
        })
        .then(function(){
            // since we are going to write Proof., we must make sure it is sent
            return (lastCommand !== "Proof.")
                ? asyncQuery("Proof.")
                : Promise.resolve()
            ;
        })
    // now we can replay the actuall proof and conclude
        .then(function() { return prooftree.replay(); })
        .then(function() { return asyncQuery("Qed.") })
        .then(function(response) {
            updateCoqtopPane(goingDown, response);
            $("#prooftree").empty();
            activeProofTree = undefined; // bad attempt at GC?
            repositionCaret();
        })
        .catch(function(error) {
            console.log(error);
        })
    ;

}

function stripWarning(s) {
    return s.replace(/^Warning: query commands should not be inserted in scripts\n/g, "");
}

function loadRemote() {

    var html = $("<div>");

    asyncListLectures(function(response) {
        var files = response.rResponse.contents;

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
                asyncLoadLecture(fileToLoad, function(response) {
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

    });

}

function loadLocal() {

    $("#filepicker").click();

}

function saveLocal() {

    var text = pweSanitizeInput($("#editor").text());
    var blob = new Blob([text], {type:'text/plain;charset=UTF-8'});
    var url = window.URL.createObjectURL(blob);
    $("#save-local-link").attr("href", url);
    $("#save-local-link")[0].click();
    $("#editor").focus();
    repositionCaret();

}

if (!String.prototype.startsWith) {
    Object.defineProperty(String.prototype, 'startsWith', {
        enumerable: false,
        configurable: false,
        writable: false,
        value: function(searchString, position) {
            position = position || 0;
            return this.lastIndexOf(searchString, position) === position;
        }
    });
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

function resetEditorWith(text) {

    proved = "";
    proving = "";
    provwill = "";

    $("#editor").append(
        $("<span>")
            .attr("id", "proved")
            .css("display", "inline")
            .css("padding", 0)
            .css("background-color", "#90EE90")
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "proving")
            .css("display", "inline")
            .css("padding", 0)
            .css("background-color", "#FFA500")
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "provwill")
            .css("display", "inline")
            .css("padding", 0)
            .css("background-color", "#ADD8E6")
    );

    $("#editor").append(
        $("<span>")
            .attr("id", "unlocked")
            .css("display", "inline")
            .css("padding", 0)
            .text(zwsp + text)
            .append('<br id=\"finalbr\"/>')
    );

}

/*
  should return an object
  {
  startSpan:   the <span> in which the focusNode lives,
  startOffset: the offset at which the selection is relative to startSpan,
  endSpan:     the <span> in which the anchorNode lives,
  endOffset:   the offset at which the selection is relative to endSpan,
  }
*/
function peacoqGetSelection() {
    var res = {};
    var sel = rangy.getSelection();

    res.startSpan = $(sel.anchorNode).closest("#editor >")[0];

    var startRange = rangy.createRange();
    startRange.selectNodeContents(res.startSpan);
    startRange.setEnd(sel.anchorNode, sel.anchorOffset);
    res.startOffset = startRange.toString().length;

    res.endSpan = $(sel.focusNode).closest("#editor >")[0];

    var endRange = rangy.createRange();
    endRange.selectNodeContents(res.endSpan);
    endRange.setEnd(sel.focusNode, sel.focusOffset);
    res.endOffset = endRange.toString().length;

    return res;
}

function adjustSelection() {
    var s = peacoqGetSelection();
    var sel = rangy.getSelection();
    var rng = sel.getRangeAt(0);

    // if there is no selection, it's easy
    if (s.startSpan === s.endSpan && s.startOffset === s.endOffset) {
        var span = s.startSpan;
        var offset = s.startOffset;
        var processing = $("#proving").text();
        var provwill = $("#provwill").text();
        if (span.id === "proved" && offset === span.textContent.length
            && processing.length === 0 && provwill.length === 0) {
            var contents = $("#unlocked").contents();
            var target = (contents.length === 0) ? $("#unlocked")[0] : contents[0];
            rng.setStart(target, 0);
            rng.setEnd(target, 0);
            sel.setSingleRange(rng);
        }
    } else {
        // TODO: a bit harder when there is a selection
    }
}

function isSelectionLocked() {
    adjustSelection();
    var s = peacoqGetSelection();
    return (s.startSpan.id !== "unlocked" || s.endSpan.id !== "unlocked");
}

function cutHandler(evt) {
    if (isSelectionLocked()) { return; }
}

function pasteHandler(evt) {
    evt.preventDefault();
    if (isSelectionLocked()) { return; }
    var clipped =
        evt.originalEvent.clipboardData.getData("text/plain")
    ;
    var sel = rangy.getSelection();
    var range = sel.getRangeAt(0);
    range.deleteContents();
    insertAtSelection(clipped);
}

/* ProofWeb */

function pweRestoreFinalBR() {
    var finalbr = $("#finalbr")[0];
    if (!finalbr) {
        $("#unlocked").append('<br id=\"finalbr\"/>');
    }
    return finalbr ? true : false;
}

function pweOptAdjustSelection() {
    if (pweSelectionLockstate() === 1) {
        pweAdjustSelection();
    }
}

function pweAdjustSelection() {
    var sel,bw,newrs;

    sel = rangy.getSelection();
    bw = sel.isBackwards();
    newrs = $.map(sel.getAllRanges(), pweAdjustRange);

    sel.removeAllRanges();
    for (var i=0; i < newrs.length; i++) {
        sel.addRange(newrs[i],bw);
    }
}

function pweAdjustRange(range) {
    var ulrange,cs,ce;

    ulrange = pweUnlockedRange();

    cs = rangy.dom.comparePoints(range.startContainer, range.startOffset,
                                 ulrange.startContainer, ulrange.startOffset);
    ce = rangy.dom.comparePoints(range.endContainer, range.endOffset,
                                 ulrange.endContainer, ulrange.endOffset);

    newrange = range.cloneRange();

    if (cs < 0) {
        newrange.setStart(ulrange.startContainer, ulrange.startOffset);
    }

    if (ce > 0) {
        newrange.setEnd(ulrange.endContainer, ulrange.endOffset);
    }

    return newrange;
}

function pweSelectionLockstate() {
    var sel = rangy.getSelection();
    return arrmax($.map(sel.getAllRanges(), pweRangeLockstate));
}

function arrmax(arr) {
    return (arr.length > 0) ? Math.max.apply(null, arr) : 0;
}

function pweRangeLockstate(range) {

    var ulrange, trange, ts;

    ulrange = pweUnlockedRange();

    if (subrange(range,ulrange)) {
        return 0; // UNLOCKED
    } else {
       trange = rangy.createRange();
       trange.setStart(range.startContainer, range.startOffset);
       trange.setEnd(ulrange.startContainer, ulrange.startOffset);
       ts = trange.toString();
       if (ts === "" || ts === zwsp) {
           return 1; // LOCKED / Adjustable
       }
       else {
           return 2; // LOCKED / Non-adjustable
       }
    }

}

function pweUnlockedRange() {
    var finalbr, ulrange;
    finalbr = $("#finalbr").get(0);
    ulrange = rangy.createRange();
    ulrange.selectNode($("#unlocked")[0]);
    ulrange.moveStart("character", 1);
    ulrange.setEndBefore(finalbr);
    return ulrange;
}

function subrange(r1, r2) {
    var intersection = intersectRanges(r1,r2);
    return intersection !== null && r1.equals(intersection);
}

function intersectRanges(r1,r2) {
    if (r1.intersectsOrTouchesRange(r2)) {
        var startComparison = rangy.dom.comparePoints(r1.startContainer, r1.startOffset, r2.startContainer, r2.startOffset),
            endComparison = rangy.dom.comparePoints(r1.endContainer, r1.endOffset, r2.endContainer, r2.endOffset);

        var intersectionRange = r1.cloneRange();
        if (startComparison == -1) {
            intersectionRange.setStart(r2.startContainer, r2.startOffset);
        }
        if (endComparison == 1) {
            intersectionRange.setEnd(r2.endContainer, r2.endOffset);
        }
        return intersectionRange;
    }
    return null;
}

function pweSelectionLocked() {
    return pweSelectionLockstate() > 0;
}

function pweGetUnlocked() {
    var ulrange;
    ulrange = pweUnlockedRange();
    return ulrange.textContent();
}

function pweSetLockedPart(part,txt) {
    $("#" + part).html(txt);
}

function pweSetUnlocked(txt) {
    $("#unlocked").html(zwsp + txt);
    pweRestoreFinalBR();
    pweCaretAtStart();
    pweFocusEditor();
}

function pweCaretAtStart() {
    pwePlaceCaret(true);
}

function pwePlaceCaret(atstart) {
    var range,sel;

    range = pweUnlockedRange();
    range.collapse(atstart);
    sel = rangy.getSelection();
    sel.setSingleRange(range);
    pweScrollToCaret();
}

function pweScrollToCaret() {
    var margin,sel,rr,nr,rects,extraheight,ct,cb,cl,cr;

    margin = 3;

    sel = rangy.getSelection();
    try {
        // use non-collapsed range, because webkit seems to prefer it.
        rr=rangy.createRange();
        rr.setStartAndEnd(sel.focusNode, sel.focusOffset);
        rr.moveStart("character",-1);

        nr=rangy.createNativeRange();
        nr.setStart(rr.startContainer, rr.startOffset);
        nr.setEnd(rr.endContainer, rr.endOffset);
        rects = nr.getClientRects();

        if (rects.length === 0) return;
        if (rr.textContent() === "\n") extraheight = rects[0].bottom - rects[0].top;
        else extraheight = 0;
        ct = arrmin($.map(rects,function(r){return r.top;}))    - margin
        cb = arrmax($.map(rects,function(r){return r.bottom;})) + margin + extraheight;
        cl = arrmin($.map(rects,function(r){return r.left;}))   - margin
        cr = arrmax($.map(rects,function(r){return r.right;}))  + margin
    } catch (e) {
        return;
    }

    function scrolldist(ve,cs,ce) {
        if (ce > ve) return ce - ve;
        if (cs < 0)  return cs;
        return 0;
    }

    var $w = $(window);
    var vt = $w.scrollTop();
    var vl = $w.scrollLeft();
    var vh = $w.height();
    var vw = $w.width();
    var newt = vt + scrolldist(vh,ct,cb);
    var newl = vl + scrolldist(vw,cl,cr);

    if (st.workaround_delay_scroll) {
        // scroll unconditionally, even if current viewport seems correct.
        setTimeout(function(){
            $w.scrollTop(newt);
            $w.scrollLeft(newl);
        }, 0);
    } else {
        if (vt !== newt) $w.scrollTop(newt);
        if (vl !== newl) $w.scrollLeft(newl);
    }
}

function pweFocusEditor() {
    if (!workaround_no_focusing) $("#editor").focus();
}

function unquote_str (oldstr) {
    var str = oldstr
        .replace(/&lt;/g, "<")
        .replace(/&gt;/g, ">")
        .replace(/&quot;/g, "\"")
        .replace(/&apos;/g, "'")
        .replace(/&amp;/g, "&")
        .replace(/<br>/g,"\n")
        .replace(/<BR>/g,"\n")
        .replace(/<BR\/>/g,"\n")
    ;
    return str;
}

function pweMoveLeft(extend) {
    var sel,newfocus,erange,bw,rs;
    var res = false;

    if (pweRelativeFocusPos()==0) {
        sel=rangy.getSelection();

        newfocus=rangy.createRange();
        newfocus.setStart(sel.focusNode,sel.focusOffset);
        newfocus.collapse(true);
        newfocus.move("character",-2)

        erange=rangy.createRange();
        erange.selectNodeContents($("#editor")[0]);

        if (subrange(newfocus,erange)) {
            if (extend) {
                bw = sel.isBackwards();
                rs = sel.getAllRanges();

                if (bw) {
                    rs[rs.length-1].moveStart("character",-2);
                } else {
                    rs[rs.length-1].moveEnd("character",-2);
                }

                sel.removeAllRanges();
                for (var i=0; i < rs.length; i++) {
                    sel.addRange(rs[i],bw);
                }
            } else {
                sel.move("character",-2);
            }
        }

        res=true;
    }

    return res;
}

function pweMoveRight(extend) {
    var sel,newfocus,erange,bw,rs;
    var res = false;

    if (pweRelativeFocusPos()==-1) {
        sel = rangy.getSelection();

        newfocus = rangy.createRange();
        newfocus.setStart(sel.focusNode, sel.focusOffset);
        newfocus.collapse(true);
        newfocus.move("character", +2);

        erange = rangy.createRange();
        erange.selectNodeContents($("#editor")[0]);

        if (subrange(newfocus,erange)) {
            if (extend) {
                bw = sel.isBackwards();
                rs = sel.getAllRanges();

                if (bw) {
                    rs[rs.length-1].moveStart("character",+2);
                } else {
                    rs[rs.length-1].moveEnd("character",+2);
                }

                sel.removeAllRanges();
                for (var i=0; i < rs.length; i++) {
                    sel.addRange(rs[i],bw);
                }
            } else {
                sel.move("character", +2);
            }
        }

        res = true;
    }

    return res;
}

function pweRelativeFocusPos() {
    var sel,ur,cp;

    sel = rangy.getSelection();
    ur = pweUnlockedRange();
    ur.collapse(true);

    cp = rangy.dom.comparePoints(sel.focusNode,sel.focusOffset,ur.startContainer,ur.startOffset);

    if (cp >= 0) {
      ur.setEnd(sel.focusNode,sel.focusOffset);
    } else {
      ur.setStart(sel.focusNode,sel.focusOffset);
    }

    return (cp * ur.toString().length)
}

function pweEmulateReturn() {
    pweInsertAtSelection("\n");
    pweScrollToCaret();
}

function pweInsertAtSelection(txt) {
    var sel, newrange;

    pweRemoveSelection();

    pweOptAdjustSelection();
    sel = rangy.getSelection();
    if (!pweSelectionLocked() && sel.rangeCount > 0) {
        newrange = pweInsertText(txt,sel.getRangeAt(0));
        sel.setSingleRange(newrange);
    }
}

function pweRemoveSelection() {
    var sel;

    pweOptAdjustSelection();
    if (!pweSelectionLocked()) {
        sel = rangy.getSelection();
        sel.deleteFromDocument();
    }
}

function pweInsertText(txt,inrange) {
    var range = inrange.cloneRange();
    var tn = document.createTextNode(txt);
    range.insertNode(tn);
    range.selectNode(tn);
    range.normalizeBoundaries();
    range.collapse(false);
    return range;
}

/*
 * decides whether we need to emulate Backspace because we are close to our
 * special character, or whether we can let the original [ev] go through
 * if [forceEmulation] is true, will definitely emulate
 */
function pweEmulateBackspace(ev, forceEmulation) {
    var range, sel;

    sel = rangy.getSelection();

    // do not emulate if not needed, so that Ctrl-Z will work
    if (!forceEmulation && sel.anchorOffset > 1 && sel.focusOffset > 1) {
        // ev will propagate and do the default
        return;
    }

    if (sel.isCollapsed) {
        range = sel.getRangeAt(0).cloneRange();
        range.moveStart("character",-1);
        if (!pweRangeLocked(range)) {
           sel.setSingleRange(range);
           sel.deleteFromDocument();
        }
    } else {
        if (!pweSelectionLocked()) { // Superfluous condition?
           sel.deleteFromDocument();
        }
    }

    ev.preventDefault();
    ev.stopPropagation();

}

function pweRangeLocked(range) {
    return pweRangeLockstate(range) > 0;
}

function pwePasteHandler(ev) {
    var cbd,txt="";

    pweOptAdjustSelection();
    if (!pweSelectionLocked()) {
        cbd = ev.originalEvent.clipboardData
            || window.clipboardData
            || st.editorwin.clipboardData
        ;
        if (cbd) {
            ev.preventDefault();
            ev.stopPropagation();
            try { txt = cbd.getData("text/plain");  } catch (e) {}
            try { txt = txt || cbd.getData("Text"); } catch (e) {}
            txt = pweSanitizeInput(txt);
            if (txt) { pweInsertAtSelection(txt); }
            pweScrollToCaret();
        } else {
            if (!st.workaround_native_paste) {
                alert("Warning: your browser does not allow access to the clipboard\n"+
                      "from the paste event handler. Attempting workaround.");
                st.workaround_native_paste=true;
            }
            setTimeout(pweCleanupPaste,0);
        }
    } else {
        ev.preventDefault();
        ev.stopPropagation();
    }
}

function pweCleanupPaste(ev) {
    var caret,range,txt,txtclean;

    caret = pweGetCaretPos();
    range = rangy.createRange();
    range.selectNodeContents($("#editor")[0]);
    range.setStartAfter($("#provwill")[0]);

    txt = range.textContent().substring(1);
    txtclean =  pweSanitizeInput(txt);
    caret -= (txt.length - txtclean.length);

    range.pasteHtml('<span id="unlocked"></span>');
    $("#unlocked").text(zwsp + txtclean);
    pweRestoreFinalBR();
    pweSetCaretPos(caret);
}

function pweSanitizeInput(txt) {
    return txt
        .replace(/\r\n/g,"\n")
        .replace(/\r/g,"\n")
        .replace(new RegExp(nbsp, 'g'), ' ')
        .replace(new RegExp(zwsp, 'g'), '')
    ;
}

function pweCutHandler(ev) {
    pweOptAdjustSelection();
    if (pweSelectionLocked()) {
        ev.preventDefault();
        ev.stopPropagation();
    }
}

function makeGroup(name, tactics) {
    return {
        "name": name,
        "tactics": _(tactics).map(function(s) { return s + '.'; }).value(),
    };
}

function lectureTactics(pt) {

    var curGoal = (isGoal(this.curNode)) ? this.curNode : this.curNode.parent;
    var curHyps = _(curGoal.hyps).map(function(h) { return h.hName; }).reverse();
    var curNames = _(curHyps).union(namesPossiblyInScope.reverse());

    var res = [
        // first, some terminators
        "reflexivity", "discriminate", "assumption", "eassumption",
        "break_if", "f_equal", "subst",

        makeGroup(
            "autos",
            ["auto", "eauto"]
        ),

        makeGroup(
            "introductions",
            ["intro", "intros"]
        ),

        makeGroup(
            "simplifications",
            ["simpl"].concat(
                _(curHyps).map(function(h) { return "simpl in " + h; }).value()
            ).concat(["simpl in *"])
        ),

        makeGroup(
            "constructors",
            ["left", "right", "split", "constructor", "econstructor", "eexists"]
        ),

        makeGroup(
            "destructors",
            _(curHyps).map(function(h) { return "destruct " + h; }).value()
        ),

        makeGroup(
            "inductions",
            _(curHyps).map(function(h) { return "induction " + h; }).value()
        ),

        makeGroup(
            "inversions",
            _(curHyps).map(function(h) { return "inversion " + h; }).value()
        ),

        makeGroup(
            "solvers",
            ["congruence", "omega", "firstorder"]
        ),

        makeGroup(
            "applications",
            _(curNames).map(function(n) { return "apply " + n; }).value()
                .concat(
                    _(curNames).map(function(n) { return "eapply " + n; }).value()
                )
        ),

        makeGroup(
            "rewrites",
            _(curNames).map(function(n) { return "rewrite -> " + n; }).value()
                .concat(
                    _(curNames).map(function(n) { return "rewrite <- " + n; }).value()
                )
        ),

        makeGroup(
            "applications in",
            _(curNames).map(function(n) {
                return _(curHyps)
                    .map(function(h) {
                        if (h === n) { return []; }
                        return ([
                            "apply " + n + " in " + h,
                            "eapply " + n + " in " + h
                        ]);
                    })
                    .flatten(true).value();
            }).flatten(true).value()
        ),

        makeGroup(
            "rewrites in",
            _(curNames).map(function(n) {
                return _(curHyps)
                    .map(function(h) {
                        if (h === n) { return []; }
                        return ([
                            ("rewrite -> " + n + " in " + h),
                            ("rewrite <- " + n + " in " + h)
                        ]);
                    })
                    .flatten(true).value()
                ;
            }).flatten(true).value()
        ),

        makeGroup(
            "reverts",
            _(curHyps).map(function(h) { return "revert " + h; }).value()
        ),

    ];

    return (
        _(res)
            .map(function(elt) {
                if ($.type(elt) === "string") {
                    return elt + ".";
                } else {
                    return elt;
                }
            })
            .value()
    );

}
