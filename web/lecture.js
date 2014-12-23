
var zwsp = "\u200B";

$(document).ready(function() {

    $("body").append(
        $("<input>")
            .attr("type", "file")
            .attr("id", "filepicker")
            .on("change", function() {
                loadFile();
                $(this).filestyle("clear"); // forces change when same file is picked
            })
    );

    $(":file").filestyle({
        badge: false,
        buttonName: "btn-primary",
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

function my_index(str) {
    return str.indexOf(".");
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

function coq_undot(str) {
    return str
        .replace(/Undo.Undo/g, 'Undo. ndo')
        .replace(/[.][.][.]/g, '__.')
        .replace(/[.][.]/g, '__')
        .replace(/[.][a-zA-Z1-9_]/g, 'AA')
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
    //pweRestoreFinalBR();
    //pweOptAdjustSelection();

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
            prover_bottom();
            break;
        case 33: // PageUp
            prover_top();
            break;
        case 13: // Enter
            prover_point();
            break;
        default:
            prevent = false;
            break;
        };

    } else {
        prevent = false;
    }

    if (prevent) {
        evt.preventDefault();
        evt.stopPropagation();
    }

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
}

function proverUp () {
    var index = 0;
    var processing = $("#processing").text();
    var typing = $("#typing").text();
    if (processing != "") {
        index = prev(processing);
    }
/*
        index = proved.length + proving.length + prev(processing);
    } else if (proving != "") {
        index = proved.length + prev(proving);
    } else if (proved != "") {
        index = prev(proved);
    }
*/
    $("#processing").text(processing.substring(0, index));
    $("#typing").text(zwsp + processing.substring(index) + typing);
    repositionCaret(1);
    //myx_undo (index, undo_cb);
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
