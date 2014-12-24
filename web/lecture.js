
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

function nl2br (str) {
    return (str + '').replace(/([^>\r\n]?)(\r\n|\n\r|\r|\n)/g, '$1<br>$2');
}

function onLoad(text) {
    // TODO: reset Coq
    // TODO: reset interface
    // TODO: parse

    var paneWidth = "50%";
    var paneHeight = "400px";

    var editorPane = $("<pre>")
        .attr("id", "editor")
        .attr("contenteditable", "true")
        .css("margin", 0)
        .css("float", "left")
        .css("width", paneWidth)
        .css("height", paneHeight)
    ;

    var coqtopPane = $("<pre>")
        .attr("id", "coqtop")
        .attr("contenteditable", "false")
        .addClass("alert")
        .css("margin", 0)
        .css("float", "left")
        .css("width", paneWidth)
        .css("height", paneHeight)
        .html("Other pane")
    ;

    $("#main").empty();
    $("#main").append(editorPane);
    $("#main").append(coqtopPane);

    $("#editor").append($("<span>").attr("id", "processed"));
    $("#editor").append($("<span>").attr("id", "processing"));
    $("#editor").append($("<span>").attr("id", "typing"));

    $("#processed")
        .css("background-color", "#90EE90")
    ;

    $("#processing")
        .css("background-color", "#ADD8E6")
    ;

    $("#processed").text("");
    $("#processing").text("");
    $("#typing").text(zwsp + text);

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
    // first the color
    switch(response.rResponse.tag) {
    case "Good":
        $("#coqtop")
            .toggleClass("alert-success", true)
            .toggleClass("alert-danger", false)
        ;
        break;
    case "Fail":
        $("#coqtop")
            .toggleClass("alert-danger", true)
            .toggleClass("alert-success", false)
        ;
        break;
    };
    // then the contents
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
    //$("#coqtop").append("\n" + JSON.stringify(response));
}

function proverDown() {
    var processing = $("#processing").text();
    var typing = $("#typing").text();
    var index = next(typing);
    if (index == 0) { return; }
    // 1 because we get rid of the zero-width spacing
    var toProcess = typing.substring(1, index);
    $("#processing").text(processing + toProcess);
    $("#typing").text(zwsp + typing.substring(index));
    repositionCaret();
    syncQuery(toProcess, updateCoqtopPane);
}

function proverUp () {
    var index = 0;
    var processing = $("#processing").text();
    var typing = $("#typing").text();
    if (processing != "") { index = prev(processing); }
    var unprocessed = processing.substring(index);
    $("#processing").text(processing.substring(0, index));
    $("#typing").text(zwsp + unprocessed + typing.substring(1));
    repositionCaret(index === 0 ? 0 : 1); // if at the start of file, no offset
    if (unprocessed !== "") { syncUndo(updateCoqtopPane); }
}

function repositionCaret(offset) {
    if (offset === undefined) { offset = 0; }
    var sel = rangy.getSelection();
    var rng = rangy.createRange();
    // 1 for the zwsp
    rng.setStart($("#typing").contents()[0], 1 + offset);
    sel.setSingleRange(rng);

    // now let's scroll so that the cursor is visible
    var cursorMargin = 40; // about two lines
    var cursorTop = $("#typing")[0].getBoundingClientRect().top;
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
