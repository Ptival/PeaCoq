function addNext(buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-down",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            onCtrlDown(true);
        })
        .append(mkGlyph("arrow-down"))
        .append(nbsp + "Next")
    ;
}

function addPrev(buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-up",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            onCtrlUp(true);
        })
        .append(mkGlyph("arrow-up"))
        .append(nbsp + "Prev")
    ;
}

function addJumpToCaret(buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "id": "prover-caret",
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            onCtrlEnter();
        })
        .append(mkGlyph("arrow-right"))
        .append(mkGlyph("italic"))
        .append(nbsp + "Go to caret")
    ;
}

function addViewEditor(buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("edit"))
            .append(nbsp + "View Editor")
        ,
        "id": "peek-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
        .on("click", focusEditorUI)
    ;
}

function addViewProofTree(buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "html": $("<span>")
            .append(mkGlyph("tree-deciduous"))
            .append(nbsp + "View Proof Tree")
        ,
        "id": "unpeek-button",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
        .on("click", focusProofTreeUI)
    ;
}

function onLoad(text) {

    asyncLog("LOAD " + text);

    $("#prooftree").empty();//.css("display", "none");
    activeProofTree = undefined;
    activeProofTrees = [];

    resetEditor(text);

    focusEditorUI();

    asyncResetCoq()
        .then(function() {
            cm.focus();
        })
        .catch(outputError);

}

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

function addLoadRemote(buttonGroup) {
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
}

function saveLocal() {
    var text = doc.getValue();
    var blob = new Blob([text], {type:'text/plain;charset=UTF-8'});
    var url = window.URL.createObjectURL(blob);
    $("#save-local-link").attr("href", url);
    $("#save-local-link")[0].click();
    cm.focus();
}

function addSaveLocal(buttonGroup) {

    $("<button>", {
        "class": "btn btn-default",
        "id": "save-local-button",
        "html": $("<span>")
            .append(mkGlyph("floppy-save"))
            .append(nbsp + nbsp + "Save"),
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

function addSettings(buttonGroup) {

    $("<button>", {
        "class": "btn btn-default",
        "data-target": "help",
        "data-toggle": "modal",
        "id": "options-button",
        "html": $("<span>")
            .append(mkGlyph("th-list"))
            .append(nbsp + nbsp + "Settings"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            $("#options").modal();
        })
    ;

    $("input:radio[name='keymap']").change(function() {
        if ($(this).is(":checked")) {
            var keyMap = $(this).val();
            cm.setOption("keyMap", keyMap);
            cmContext.setOption("keyMap", keyMap);
            cmResponse.setOption("keyMap", keyMap);
        }
    });

    // $("#set-printing-all").change(function() {
    //     if($(this).is(":checked")) {
    //         asyncRequest('setprintingall', undefined);
    //     } else {
    //         asyncRequest('unsetprintingall', undefined);
    //     }
    // });

}

function addHelp(buttonGroup) {
    $("<button>", {
        "class": "btn btn-default",
        "data-target": "help",
        "data-toggle": "modal",
        "id": "feedback-button",
        "html": $("<span>")
            .append(mkGlyph("question-sign"))
            .append(nbsp + nbsp + "Help"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            $("#help").modal();
        })
    ;
}

function addFeedback(buttonGroup) {

    $("<button>", {
        "class": "btn btn-info",
        "data-target": "feedback",
        "data-toggle": "modal",
        "id": "feedback-button",
        "html": $("<span>")
            .append(mkGlyph("bullhorn"))
            .append(nbsp + nbsp + "Feedback"),
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

}

function addAskHelp(buttonGroup) {

    $("<button>", {
        "class": "btn btn-primary",
        "id": "ask-for-help-button",
        "html": $("<span>")
            .append(mkGlyph("user"))
            .append(nbsp + nbsp + "Ask for help"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            asyncLog("NEEDHELP");
            $("#ask-for-help-button").css("display", "none");
            $("#asked-for-help-button").css("display", "");
        })
    ;

    $("<button>", {
        "class": "btn btn-primary",
        "id": "asked-for-help-button",
        "html": $("<span>")
            .append(mkGlyph("user"))
            .append(nbsp + nbsp + "You asked for help"),
    })
        .appendTo(buttonGroup)
        .css("display", "none")
    ;

    $("<button>", {
        "class": "btn btn-danger",
        "id": "help-in-progress-button",
        "html": $("<span>")
            .append(mkGlyph("user"))
            .append(nbsp + nbsp + "Help in progress, click here when done!"),
    })
        .appendTo(buttonGroup)
        .css("display", "none")
        .on("click", function() {
            asyncLog("HELPEND");
            $(this).css("display", "none");
            $("#ask-for-help-button").css("display", "");
            $("#asked-for-help-button").css("display", "none");
        })
    ;

}

function addScreenshot(buttonGroup) {

    $("<button>", {
        "class": "btn btn-default",
        "data-target": "help",
        "data-toggle": "modal",
        "id": "screenshot-button",
        "html": $("<span>")
            .append(mkGlyph("camera"))
            .append(nbsp + nbsp + "Screenshot"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {

            //This code takes a screenshot of the SVG with embedded HTML
            $("svg")[0].toDataURL("image/png", {
                "callback": function(url) {
                    $("#save-screenshot").attr("href", url);
                    $("#save-screenshot")[0].click();
                    cm.focus();
                },
                "keepNonSafe": true,
            });

            // var transform = $("#viewport").attr("transform");
            // $("#viewport").attr("transform", "");
            // $("svg body").each(function() {
            //     var self = this;
            //     html2canvas($(self).children(0), {
            //         "allowTaint": true,
            //         "onrendered": function(canvas) {
            //             var copy = document.createElement("canvas");
            //             copy.getContext("2d").drawImage(canvas, 0, 0);
            //             var c = canvas.getContext("2d");
            //             var tx = SVGTransformX($("#viewport"));
            //             var ty = SVGTransformY($("#viewport"));
            //             c.setTransform(1, 0, 0, 1, 0, 0);
            //             c.clearRect(0, 0, canvas.width, canvas.height);
            //             c.translate(tx, ty);
            //             c.drawImage(copy, 0, 0);
            //             $(self).children(0).replaceWith(canvas);
            //         },
            //     });
            // });
            // $("#viewport").attr("transform", transform);

            // //canvg();

            // html2canvas($("body"), {
            //     "allowTaint": true,
            //     "onrendered": function(canvas) {
            //         var url = canvas.toDataURL();
            //         $("#save-screenshot").attr("href", url);
            //         $("#save-screenshot")[0].click();
            //         cm.focus();
            //     },
            // });

        })
    ;

    $("<a>", {
        "download": "screenshot.png",
        "id": "save-screenshot",
    })
        .css("display", "none")
        .appendTo(buttonGroup)
    ;

}

function addCaptureDiffs(buttonGroup) {

    $("<button>", {
        "class": "btn btn-default",
        "data-target": "help",
        "data-toggle": "modal",
        "id": "diffs-button",
        "html": $("<span>")
            .append(mkGlyph("camera"))
            .append(nbsp + nbsp + "Capture diffs"),
    })
        .appendTo(buttonGroup)
        .on("click", function() {
            captureDiffs();
        })
    ;

}
