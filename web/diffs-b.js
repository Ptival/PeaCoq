var first = 0;
var last = 10;

var current = first;

var startTime;

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

    addPrevious(cm, buttonGroup);
    addNext(cm, buttonGroup);
    
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
    displayDiff();
}

function onAfter(cm) {
    displayDiff();
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

function displayDiff() {
    $("#main-bottom").html(
        '<img id="picture" src="coq/diffs/screenshot ('
            + current + ').png"/>'
    );
    $("#main-bottom").height(
        $("body").height() - $("#main-top").height() - $("#toolbar").height() - 2
    );
}
