var first = 2;
var last = 12;

var current = first;

var startTime;

// processingAsyncRequests should take this as an argument...
var editorOnRequestTriggered = function() { }
var editorOnResponse = function() { }

$(document).ready(function() {
    
    cm = CodeMirror(
        $("#coqtop-context")[0],
        {
            "gutters": [],
            "lineNumbers": true,
            "lineWrapping": true,
            "matchBrackets": true,
            "mode": "text/x-coq",
        }
    );

    var buttonGroup = $("#toolbar > .btn-group");

    addBefore(cm, buttonGroup);
    addAfter(cm, buttonGroup);

    //addPrevious(cm, buttonGroup);
    //addNext(cm, buttonGroup);

    addTitle(buttonGroup);

    onPrevious(cm);

    $("#form").submit(function() {

        if (!$("#goal-changed-yes").is(":checked")
            &&
            !$("#goal-changed-yes").is(":checked")
        ) {
            alert("Please select whether the goal has changed.");
            return false;
        }

        var stopTime = Date.now();
        var deltaTime = stopTime - startTime;
        if (deltaTime < 1000) {
            alert("Accidental click detected and ignored.");
            return false;
        }
        startTime = stopTime;

        var removed = $("#input-removed").val();
        var added = $("#input-added").val();
        var changed = $("#input-changed").val();
        var goalChanged = $("#goal-changed").is(":checked");

        // TODO: send to backend
        console.log(deltaTime, removed, added, changed, goalChanged);
        asyncLog(deltaTime + "," + removed + "," + added + "," + changed + ","
                 + goalChanged);

        if (current !== last) {
            onNext(cm);
        } else {
            $('#stopModal').modal('show');
        }

        return false;
    });

    $('#startModal').modal('show');

    $("#start").click(function() {
        startTime = Date.now();
    });

    $('#stopModal').on('hidden.bs.modal', function () {
        $("body").text("That's all folks! You can close this window.");
    })

});

function updateTitle() {
    $("#title").text(allDiffs[current].tactic);
}

function resetForm() {
    $("#input-removed").val("");
    $("#input-added").val("");
    $("#input-changed").val("");
    $("#goal-changed").prop("checked", false);
}

function onBefore(cm) {
    renderContext(cm, allDiffs[current].before);
    $("#before").prop("disabled", true);
    $("#after").prop("disabled", false);
}

function onAfter(cm) {
    renderContext(cm, allDiffs[current].after);
    $("#before").prop("disabled", false);
    $("#after").prop("disabled", true);
}

function onPrevious(cm) {
    current = Math.max(current - 1, first);
    $("#previous").prop("disabled", current === first);
    $("#next").prop("disabled", current === last);
    updateTitle()
    onBefore(cm);
}

function onNext(cm) {
    current = Math.min(current + 1, last);
    $("#previous").prop("disabled", current === first);
    $("#next").prop("disabled", current === last);
    updateTitle();
    onBefore(cm);
    resetForm();
}

function addTitle(buttonGroup) {
    $("<button>", {
        "class": "btn btn-info",
        "disabled": true,
        "id": "title",
    })
        .appendTo(buttonGroup)
    ;
}

function addBefore(cm, buttonGroup) {

    $("<button>", {
        "class": "btn btn-default",
        "id": "before",
    })
        .appendTo(buttonGroup)
        .on("click", _.partial(onBefore, cm))
        .append(mkGlyph("backward"))
        .append(nbsp + "Before")
    ;

    $("<button>", {
        "class": "btn btn-default",
    })
        .appendTo($("#before-placeholder"))
        .append(mkGlyph("backward"))
        .append(nbsp + "Before")
    ;

}

function addAfter(cm, buttonGroup) {

    $("<button>", {
        "class": "btn btn-default",
        "id": "after",
    })
        .appendTo(buttonGroup)
        .on("click", _.partial(onAfter, cm))    
        .append(mkGlyph("forward"))
        .append(nbsp + "After")
    ;

    $("<button>", {
        "class": "btn btn-default",
    })
        .appendTo($("#after-placeholder"))
        .append(mkGlyph("forward"))
        .append(nbsp + "After")
    ;

}

function addPrevious(cm, buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "id": "previous",
    })
        .appendTo(buttonGroup)
        .on("click", _.partial(onPrevious, cm))
        .append(mkGlyph("fast-backward"))
        .append(nbsp + "Prev")
    ;
}

function addNext(cm, buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "id": "next",
    })
        .appendTo(buttonGroup)
        .on("click", _.partial(onNext, cm))
        .append(mkGlyph("fast-forward"))
        .append(nbsp + "Next")
    ;
}

function mkGlyph(name) {
    return $("<i>", {
        "class": "glyphicon glyphicon-" + name,
    });
}

function showHypothesisText(h) {
    var res = h.hName;
    if (h.hValue !== null) {
        res = res + " := " + showTermText(h.hValue);
    }
    res = res + " : " + showTermText(h.hType);
    return res;
}

/*
  Fill a [CodeMirror] instance [cm] with the context for a given [response].
 */
function renderContext(cm, response) {
    var value = "";

    switch (response.response.tag) {
    case "Good":
        var nbFocused = response.focused.length;
        if (response.focused.length > 0) {

            _(response.focused[0].gHyps).each(function(h) {
                var hyp = extractHypothesis(h);
                var currentLinePosition = value.split('\n').length;
//                cm.setGutterMarker(currentLinePosition + 1, "context-gutter",
//                                   $("<span class='gutterspan'>").text(hyp.hName));
                value += showHypothesisText(hyp) + "\n";
            });

            // the goal line position must be computed now
            var goalLinePosition = value.split('\n').length;

            value += showTermText(extractGoal(response.focused[0].gGoal));

            cm.getDoc().setValue(value);

            cm.addLineWidget(
                goalLinePosition - 1,
                $("<hr>").css("border", "1px solid black")[0],
                /*
                $("<div>")
                    .text("__________________________________________________")
                [0],
                */
                { "above": true }
            );

        } else {

            alert("This should not happen");

        }
        break;
    case "Fail":
        break;
    }
}
