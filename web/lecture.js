"use strict";

var processing = false;
var nbsp = "\u00A0";
var zwsp = "\u200B";
var namesPossiblyInScope = [];
var focusedOnEditor = true;
var activeProofTrees = [];

var unicodeList = [
    ("forall", "∀"),
    ("\/", "∨"),
    ("/\\", "∧"),
    ("neg", "¬"),
];

$(document).ready(function() {

    $(window).bind('beforeunload', function(){
        return 'WARNING: unsaved progress wil be lost';
    });

    var buttonGroup = $(".btn-group");

    addPrev(buttonGroup);
    addNext(buttonGroup);
    addJumpToCaret(buttonGroup);
    addViewEditor(buttonGroup);
    addViewProofTree(buttonGroup);

    // Temporarily disabled
    // addLoadRemote(buttonGroup);
    addLoadLocal(buttonGroup);
    addSaveLocal(buttonGroup);
    addSettings(buttonGroup);
    addHelp(buttonGroup);

    // addFeedback(buttonGroup);
    // addAskHelp(buttonGroup);

    // addScreenshot(buttonGroup);
    // addCaptureDiffs(buttonGroup);

    $("<button>", {
        "class": "btn btn-default",
        "html": '<img src="media/ajax-loader.gif" /><span id="loading-text"></span>',
        "id": "loading",
    })
        .appendTo(buttonGroup)
        .css("display", "none")
    ;

    //resize();
    $(window).resize(resize);

    $("body")
        .on("keydown", globalKeyHandler)
    ;

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

function resize() {
    var windowHeight = $(window).height();
    // careful, there are many <body> when using proof tree!
    //$("html > body").height(windowHeight);
    //var height = windowHeight - $("#toolbar").height();
    //height = Math.floor(height / 2);
    //$("#editor").css("height", height);
    //$("#coqtop").css("height", height);
    //$("#prooftree").css("height", height);
    //$("#pt-1").css("height", height);
    //$("svg").css("height", height);
    // TODO: fix height bug
    var width = $(window).width();
    var height = $("#prooftree").height();
    if (activeProofTree !== undefined) {
        activeProofTree.resize($(window).width(), height);
    }
    resizeCoqtopPanes();
    scrollIntoView();
}

function resizeCoqtopPanes() {

    if (focusedOnEditor) {

        var contextLength = docContext.getValue().length;
        var responseLength = docResponse.getValue().length;

        if (contextLength === 0 && responseLength === 0) {
            $("#coqtop-context").height("50%");
            $("#coqtop-response").height("50%");
        } else if (contextLength === 0) {
            $("#coqtop-context").height("0%");
            $("#coqtop-response").height("100%");
        } else if (responseLength === 0) {
            $("#coqtop-context").height("100%");
            $("#coqtop-response").height("0%");
        } else {
            $("#coqtop-context").height("80%");
            $("#coqtop-response").height("20%");
        }

    } else {

        $("#coqtop-context").height("0%");
        $("#coqtop-response").height("100%");

    }

}

// Some of this code has been borrowed from the ProofWeb project
// Their license is unclear, TODO make sure we can borrow, oops!
var delimiters = ['.'];
function my_index(str) {
    var index = +Infinity;
    _(delimiters).each(function(delimiter) {
        var pos = str.indexOf(delimiter);
        if (pos >= 0 && pos < index) { index = pos; }
    });
    if (index !== +Infinity) { return index; }
    else { return -1; }
}

var bullets = ["{", "}", "+", "-", "*"];

function next(str) {
    // if the very next thing is one of {, }, +, -, *, it is the next
    var trimmed = coqTrimLeft(str);
    if (_(bullets).contains(trimmed[0])) {
        return str.length - trimmed.length + 1;
    }
    // otherwise, gotta find a dot
    return coq_find_dot(coq_undot(str), 0) + 1;
}

// TODO: this is a bit hacky
function prev(str) {
    // remove the last delimiter, since we are looking for the previous one
    var str = str.substring(0, str.length - 1);
    var lastDotPosition = coq_find_last_dot(coq_undot(str), 0);
    // now, it could be the case that there is a bullet after that dot
    var strAfterDot = str.substring(lastDotPosition + 1, str.length);
    var firstCharAfterDot = coqTrimLeft(strAfterDot)[0];
    if (_(bullets).contains(firstCharAfterDot)) {
        return lastDotPosition + 1 + strAfterDot.indexOf(firstCharAfterDot) + 1;
    }
    // otherwise, find the last dot
    return coq_find_last_dot(coq_undot(str), 0) + 1;
}

function count(str, pat) {
    var arr = str.split(pat);
    return (arr.length);
}

// highlight dot that are terminators as opposed to the others
function coq_undot(str) {
    str = str.replace(/[.][.][.]/g, '__.'); // emphasize the last dot of ...
    str = str.replace(/[.][.]/g, '__'); // hides .. in notations
    str = str.replace(/[.][a-zA-Z1-9_\(]/g, '__'); // hides qualified identifiers
    // hide curly braces that are implicit arguments
    //str = str.replace(/\{((?:[^\.\}]|\.(?!\s))*)\}/g, "_$1_");
    // make other braces look like periods
    //str = str.replace(/[\{\}]/g, ".");
    return str;
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
    //console.log(evt.keyCode);
    if (evt.ctrlKey) {
        switch(evt.keyCode) {
        default:
            break;
        }
    }
}

var goingDown = true, goingUp = false;

function updateCoqtopPane(direction, response) {

    var toprove = getToprove();
    if (toprove.length !== 0) {
        docContext.setValue("");
        docResponse.setValue("");
        return;
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

    var contextContents = "";

    switch (response.rResponse.tag) {

    case "Good":

        var nbFocused = response.rGoals.focused.length;
        var unfocused = response.rGoals.unfocused[0];

        if (nbFocused > 0) {

            _(response.rGoals.focused[0].gHyps).each(function(h) {
                contextContents += PT.showHypothesisText(extractHypothesis(h)) + "\n";
            });

            var goalLinePosition = contextContents.split('\n').length;

            contextContents += showTermText(extractGoal(response.rGoals.focused[0].gGoal));
            contextContents += "\n\n";

            var nbUnfocused = (unfocused === undefined)
                ? 0
                : unfocused[0].length + unfocused[1].length
            ;

            if (nbUnfocused === 0) {
                contextContents += nbFocused + " subgoal" + (nbFocused <= 1 ? "" : "s");
            } else {
                contextContents += (
                    nbFocused + " focused subgoal" + (nbFocused <= 1 ? "" : "s")
                        + ", " + nbUnfocused + " unfocused"
                );
            }

            _(response.rGoals.focused)
                .rest()
                .each(function(g, ndx) {
                    contextContents += "\n\n";
                    contextContents += "subgoal " + (ndx + 2) + "\n";
                    contextContents += showTermText(extractGoal(g.gGoal));
                })
            ;

            docContext.setValue(contextContents);

            cmContext.addLineWidget(
                goalLinePosition - 1,
                //$("<hr>").css("border", "1px solid black")[0],
                $("<div>")
                    .text("__________________________________________________")
                [0],
                { "above": true }
            );

            // _(response.rGoals.focused[0].gHyps).each(function(h, ndx) {

            //     var h = extractHypothesis(h);

            //     var div = $("<div>")
            //         .attr("class", "btn-group dropdown")
            //         .css("position", "relative")
            //     ;

            //     div.append(
            //         $("<button>")
            //             .attr("class", "btn btn-default btn-sm dropdown-toggle")
            //             .attr("data-toggle", "dropdown")
            //             .attr("aria-expanded", "false")
            //             .html('<span class="caret"></span>')
            //     );

            //     var ul = $("<ul>")
            //         .attr("class", "dropdown-menu pull-left")
            //         .css("height", "auto !important")
            //         .css("overflow", "visible !important")
            //         .attr("role", "menu")
            //     ;

            //     div.append(ul);

            //     _(["clear", "destruct", "generalize", "induction", "revert", "very long name for a tactic"])
            //         .each(function(item) {
            //             ul.append(
            //                 $("<li>").append(
            //                     $("<a>")
            //                         .attr("href", "#")
            //                         .text(item + ' ' + h.hName + '.')
            //                 )
            //             );
            //         })
            //     ;

            //     cmContext.setGutterMarker(
            //         ndx,
            //         "tactic-gutter",
            //         div[0]
            //     );

            // });

        } else if (unfocused !== undefined) {

            var nbRemaining = unfocused[0].length + unfocused[1].length;

            contextContents += (
                nbRemaining + " remaining subgoal" + (nbRemaining <= 1 ? "" : "s")
            );

            docContext.setValue(contextContents);

        } else {

            docContext.setValue(contextContents);

        }

        break;

    case "Fail":

        break;

    };

    var responseContents = stripWarning(contents);

    // postprocessing of Inductive
    if (responseContents.startsWith("Inductive")) {
        responseContents = responseContents
            .replace(/:=\s+/, ":=\n| ")
            .replace(/ \| /, "\n| ")
        ;
    }

    docResponse.setValue(responseContents);

}

function undoCallback(fromUser, undone, response) {
    switch(response.rResponse.tag) {
    case "Good":
        if (activeProofTree !== undefined) {
            activeProofTree.onUndo(fromUser, undone, response);
        }
        var stepsToRewind = + response.rResponse.contents[0];
        //console.log("Rewinding additional " + stepsToRewind + " steps");
        while (stepsToRewind-- > 0) {
            var rProved = mProved.find();
            var rUnlocked = mUnlocked.find();
            var proved = doc.getRange(rProved.from, rProved.to);
            if (proved === "") { return; }
            var prevIndex = prev(proved);
            var pieceUnproved = proved.substring(prevIndex);
            if (pieceUnproved === "") { return; }
            var prevPos = cm.findPosH(rProved.from, prevIndex, "char");
            markProved(rProved.from, prevPos);
            markProving(prevPos, prevPos);
            markToprove(prevPos, prevPos);
            markUnlocked(prevPos, rUnlocked.to);
            if (fromUser) {
                doc.setCursor(prevPos);
                scrollIntoView();
            }
        }
        response.rResponse.contents[0] = ""; // don't show the user the steps number
        break;
    };
    updateCoqtopPane(goingUp, response);
}

var safeDelimiters = [' ', '\n'];

/*
 * Prepends [command] to [provwill], making sure that it is separated from the
 * previous text and the next text.
 */
function safePrependToprove(command) {

    // if the command does not start with a space, and the last thing did not
    // end with a newline or space, let's make some room
    var stringBefore = getProved() + getProving();
    if (stringBefore !== "") {
        var characterBefore = stringBefore[stringBefore.length - 1];
        var characterAfter = command[0];
        if (!_(safeDelimiters).contains(characterBefore)
            && !_(safeDelimiters).contains(characterAfter)) {
            command = ' ' + command;
        }
    }

    // if the command does not end with a space, and the next thing does not
    // start with a newline or space, let's make some room
    var stringAfter = getToprove() + getUnlocked();
    if (stringAfter !== "") {
        var characterBefore = command[command.length - 1];
        var characterAfter = stringAfter[0];
        if (!_(safeDelimiters).contains(characterBefore)
            && !_(safeDelimiters).contains(characterAfter)) {
            var rUnlocked = mUnlocked.find();
            doc.replaceRange(" ", rUnlocked.from);
        }
    }

    var rProving = mProving.find();
    var rToprove = mToprove.find();
    var rUnlocked = mUnlocked.find();
    mToprove.inclusiveLeft = false;
    doc.replaceRange(command, rToprove.from);
    mToprove.inclusiveLeft = true;
    markToprove(rProving.to, rUnlocked.from);
    // if rToprove was empty, the last command actually inserted into unlocked
    if (getToprove() === "") {
        var rUnlocked = mUnlocked.find();
        var newPos = cm.findPosH(rUnlocked.from, command.length, "char");
        markToprove(rToprove.from, newPos);
        markUnlocked(newPos, rUnlocked.to);
    }

}

function mkGlyph(name) {
    return $("<i>", {
        "class": "glyphicon glyphicon-" + name,
    });
}

function focusEditorUI() {

    focusedOnEditor = true;

    $("#main").height("100%");
    $("#prooftree").height("0%");

    $("#peek-button").css("display", "none");
    $("#unpeek-button").css("display", "");

    resize();
    cm.refresh();
    scrollIntoView();
    cm.focus();

}

function focusProofTreeUI() {

    focusedOnEditor = false;

    $("#main").height("30%");
    $("#prooftree").height("70%");

    $("#peek-button").css("display", "");
    $("#unpeek-button").css("display", "none");

    $("#coqtop-context").height("0%");
    $("#coqtop-response").height("100%");

    resize();
    cm.refresh();
    scrollIntoView();
    activeProofTree.getFocus();
    activeProofTree.refreshTactics();

}

function createProofTree(response) {

    activeProofTree = new ProofTree(
        $("#prooftree")[0],
        $(window).width(),
        $("#prooftree").height(),
        function() { $("#loading").css("display", ""); },
        function() { $("#loading").css("display", "none"); }
    );

    activeProofTree.newAlreadyStartedTheorem(
        response,
        //replayTactics
        //replayAndStudyTactics
        //studyTactics
        studyTacticsV2
    );

    // only show up the tree automatically if the user is not processing to
    // caret
    var toprove = getToprove();
    if (toprove.length === 0) {
        focusProofTreeUI();
        activeProofTree.refreshTactics();
    }

    if (autoLayout) {
        // do not insert Proof. when processing file further
        if (toprove.length === 0) {
            proofTreeQueryWish("Proof.");
        }

        // TODO: insert a newline only when needed...
        //var rUnlocked = mUnlocked.find();
        //doc.replaceRange('\n  ', rUnlocked.from);

        activeProofTree.getFocus();
    }

}

function exitProofTree() {
    activeProofTree.div.remove();
    activeProofTree = activeProofTrees.pop(); // keep this line before focusEditorUI
    if (activeProofTree === undefined) {
        focusEditorUI();
    } else {
        activeProofTree.div.style("display", "");
    }
    asyncLog("EXITPROOFTREE");
}

function stripWarning(s) {
    return s.replace(/^Warning: query commands should not be inserted in scripts\n/g, "");
}

function makeGroupNoPeriod(name, tactics) {
    return {
        "name": name,
        "tactics": _(tactics).map(function(s) { return s; }).value(),
    };
}

function makeGroup(name, tactics) {
    return {
        "name": name,
        "tactics": _(tactics).map(function(s) { return s + '.'; }).value(),
    };
}

// TODO: this does not deal properly with bullets :(
function incomingTactic() {
    var rToprove = mToprove.find();
    var toprove = doc.getRange(rToprove.from, rToprove.to);
    if (toprove !== "") {
        var nextIndex = next(toprove);
        return coqTrim(toprove.substring(0, nextIndex));
    }
    var rUnlocked = mUnlocked.find();
    var unlocked = doc.getRange(rUnlocked.from, rUnlocked.to);
    var nextIndex = next(unlocked);
    var trimmed = coqTrim(unlocked.substring(0, nextIndex));

    return trimmed;
}

function safeIncomingTactic() {
    var res = incomingTactic();
    if (isVernacularCommand(res)) {
        return undefined;
    }
    return res;
}

function replayAndStudyTactics(pt) {
    return replayTactics(pt).concat(studyTactics(pt));
}

/*
  This strategy returns only the tactic that is coming next in the file, making
  it easy to replay an entire file by just always picking the tactic that
  appears.
*/
function replayTactics(pt) {
    var t = safeIncomingTactic();
    return (t
            ? [makeGroupNoPeriod("incoming", [t])]
            : []
           );
}

function onlyRightRewrite(s) {
    switch (s) {
    case "concat_nil_left":
    case "concat_nil_right":
    case "rev_involutive":
        return true;
    default:
        return false;
    }
}

function noApply(s) {
    switch (s) {
    case "concat_nil_left":
        return true;
    default:
        return false;
    }
}

var tacticsLeftRight = false;
var tacticsApply = false;
var tacticsSplit = false;
var tacticsCasesContradiction = false;
var tacticsSimplInStar = false;

function singleton(g) { return makeGroup(g, [g]); }

function addRightRewrite(pt, res, name) {
    if (pt.curNode.parentTactic === undefined) {
        res.push(singleton("rewrite -> " + name));
    } else {
        if (pt.curNode.parentTactic.tactic !== "rewrite <- " + name + ".") {
            res.push(singleton("rewrite -> " + name));
        }
    }
}

function addLeftRewrite(pt, res, name) {
    if (pt.curNode.parentTactic === undefined) {
        res.push(singleton("rewrite <- " + name));
    } else {
        if (pt.curNode.parentTactic.tactic !== "rewrite -> " + name + ".") {
            res.push(singleton("rewrite <- " + name));
        }
    }
}

function studyTacticsV2(pt) {
    var curGoal = (isGoal(pt.curNode)) ? pt.curNode : pt.curNode.parent;
    // reverse is in place, so clone is needed
    var curHypsFull = _(curGoal.hyps).clone().reverse();
    var curHyps = _(curHypsFull).map(function(h) { return h.hName; });
    var curNames = _(curHyps).union(namesPossiblyInScope.reverse());

    var falseInHyps = _(curHypsFull).some(function(h) {
        return (h.hType.tag === "Var" && h.hType.contents === "False");
    });

    var res = [
        singleton("simpl"),
        singleton("intros"),
    ];

    if (tacticsSimplInStar) { res.push(singleton("simpl in *")); }

    if (pt.goalIsReflexive()) { res.push(singleton("reflexivity")); }

    if (tacticsCasesContradiction) {
        if (falseInHyps) {
            res.push(singleton("contradiction"));
        }
        _(curHypsFull).each(function(h) {
            if (pt.hypIsDisjunction(h)) {
                res.push(singleton("cases " + h.hName));
            }
        });
    }

    if (tacticsLeftRight && pt.goalIsDisjunction()) {
        res.push(singleton("left"));
        res.push(singleton("right"));
    }

    if (tacticsSplit && pt.goalIsConjunction()) {
        res.push(singleton("split"));
    }

    if (tacticsApply) {
        _(curNames)
            .each(function(n) {
                if (!noApply(n)) {
                    res.push(singleton("apply " + n));
                }
            });
    }

    // TODO: not rewrite the exact opposite of last rewrite
    _(curNames)
        .each(function(n) {
            if (onlyRightRewrite(n)) {
                addRightRewrite(pt, res, n);
            } else {
                addRightRewrite(pt, res, n);
                addLeftRewrite(pt, res, n);
            }
        })
    ;

    if (tacticsSimplInStar) {
        res.push(singleton("simpl in *", ["simpl in *"]));
    }

    _(curHypsFull)
        .filter(function(h) {
            return h.hType.tag === "Var" && h.hType.contents === "natlist";
        })
        .each(function(h) {
            res.push(singleton("induction " + h.hName));
        });

    return res;

}

function studyTactics(pt) {

    var curGoal = (isGoal(pt.curNode)) ? pt.curNode : pt.curNode.parent;
    var curHypsFull = _(curGoal.hyps).clone().reverse();
    var curHyps = _(curHypsFull).map(function(h) { return h.hName; });
    var curNames = _(curHyps).union(namesPossiblyInScope.reverse());

    var res = [

        makeGroup(
            "terminators",
            (pt.goalIsReflexive() ? ["reflexivity"] : [])
                .concat(tacticsCasesContradiction ? ["contradiction"] : [])
                .concat([
                    //"discriminate",
                    //"assumption",
                ])
        ),

        makeGroup(
            "autos",
            [
                //"auto",
                //"eauto",
            ]
        ),

        makeGroup(
            "introductions",
            ["intros", "intro"]
        ),

        makeGroup(
            "break_if, f_equal, subst",
            [
                "break_if",
                //"f_equal",
                //"repeat f_equal",
                "subst"
            ]
        ),

        makeGroup(
            "simplifications",
            ["simpl"]
                .concat(
                    (pt.curNode.hyps.length > 0 ? ["simpl in *"] : [])
                )
                .concat(
                    _(curHyps).map(function(h) { return "simpl in " + h; }).value()
                )
        ),

        makeGroup(
            "constructors",
            ((tacticsLeftRight && pt.goalIsDisjunction()) ? ["left", "right"] : [])
                .concat((tacticsSplit && pt.goalIsConjunction()) ? ["split"] : [])
                .concat([
                    //"constructor",
                    //"econstructor",
                    //"eexists",
                ])
        ),

        makeGroup(
            "destructors",
            []
                .concat(
                    tacticsCasesContradiction ?
                    _(curHypsFull).map(function(h) {
                        return pt.hypIsDisjunction(h) ? ["cases " + h.hName] : [];
                    }).value()
                    : []
                )
                // .concat(
                //     _(curHypsFull).map(function(h) {
                //         return pt.hypIsConjunction(h) ? ["destruct " + h.hName] : [];
                //     }).value()
                // )
        ),

        makeGroup(
            "rewrites",
            _(curNames)
                .map(function(n) {
                    if (onlyRightRewrite(n)) {
                        return ["rewrite -> " + n];
                    } else {
                        return [
                            "rewrite -> " + n,
                            "rewrite <- " + n
                        ];
                    }
                })
                .flatten(true).value()
        ),

        // makeGroup(
        //     "destructors",
        //     _(curHyps)
        //         .filter(function(h) { return isLowerCase(h[0]); })
        //         .map(function(h) { return "destruct " + h; })
        //         .value()
        // ),

        makeGroup(
            "inductions",
            _(curHypsFull)
                .filter(function(h) {
                    return h.hType.tag === "Var" && h.hType.contents === "natlist";
                })
                .map(function(h) { return "induction " + h.hName; })
                .value()
        ),

        // makeGroup(
        //     "inversions",
        //     _(curHyps).map(function(h) { return "inversion " + h; }).value()
        // ),

        makeGroup(
            "solvers",
            [
                //"congruence",
                //"omega",
                //"firstorder"
            ]
        ),

        makeGroup(
            "applications",
            tacticsApply ? (
                _(curNames).map(function(n) { return "apply " + n; }).value()
                // .concat(
                //     _(curNames).map(function(n) { return "eapply " + n; }).value()
                // )
            ) : []
        ),

        makeGroup(
            "applications in",
            _(curNames).map(function(n) {
                return _(curHyps)
                    .map(function(h) {
                        if (h === n) { return []; }
                        return ([
                            "apply " + n + " in " + h,
                            //"eapply " + n + " in " + h,
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
                        if (onlyRightRewrite(n)) {
                            return ["rewrite -> " + n + " in " + h];
                        } else {
                            return ([
                                ("rewrite -> " + n + " in " + h),
                                ("rewrite <- " + n + " in " + h)
                            ]);
                        }
                    })
                    .flatten(true).value()
                ;
            }).flatten(true).value()
        ),

        // makeGroup(
        //     "reverts",
        //     _(curHyps).map(function(h) { return "revert " + h; }).value()
        // ),

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

/*
  This strategy tries many tactics, not trying to be smart.
*/
function lectureTactics(pt) {

    var curGoal = (isGoal(pt.curNode)) ? pt.curNode : pt.curNode.parent;
    var curHypsFull = _(curGoal.hyps).clone().reverse();
    var curHyps = _(curHypsFull).map(function(h) { return h.hName; });
    var curNames = _(curHyps).union(namesPossiblyInScope.reverse());

    var res = [

        makeGroup(
            "terminators",
            (pt.goalIsReflexive() ? ["reflexivity"] : [])
                .concat([
                    "discriminate",
                    "assumption",
                    "eassumption",
                ])
        ),

        makeGroup(
            "autos",
            ["auto", "eauto"]
        ),

        makeGroup(
            "introductions",
            ["intros", "intro"]
        ),

        makeGroup(
            "break_if, f_equal, subst",
            [
                "break_if",
                "f_equal",
                "repeat f_equal",
                "subst"
            ]
        ),

        makeGroup(
            "simplifications",
            ["simpl"].concat(
                _(curHyps).map(function(h) { return "simpl in " + h; }).value()
            ).concat(
                (pt.curNode.hyps.length > 0 ? ["simpl in *"] : [])
            )
        ),

        makeGroup(
            "constructors",
            (pt.goalIsDisjunction() ? ["left", "right"] : [])
                .concat(pt.goalIsConjunction() ? ["split"] : [])
                .concat([
                    "constructor",
                    "econstructor",
                    "eexists",
                ])
        ),

        makeGroup(
            "destructors",
            _(curHyps)
                .filter(function(h) { return isLowerCase(h[0]); })
                .map(function(h) { return "destruct " + h; })
                .value()
        ),

        makeGroup(
            "inductions",
            _(curHypsFull)
                .filter(function(h) {
                    return h.hType.tag === "Var" && h.hType.contents === "natlist";
                })
                .map(function(h) { return "induction " + h.hName; })
                .value()
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
            _(curNames)
                .map(function(n) {
                    return ["rewrite -> " + n, "rewrite <- " + n];
                })
                .flatten(true).value()
        ),

        makeGroup(
            "applications in",
            _(curNames).map(function(n) {
                return _(curHyps)
                    .map(function(h) {
                        if (h === n) { return []; }
                        return ([
                            "apply " + n + " in " + h,
                            "eapply " + n + " in " + h,
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

/*
 * For the following callbacks, the assumption is that they may be triggered
 * either as a response from the editor asking for some request to be performed,
 * or from the proof tree asking for some request to be performed. As a result,
 * things that should happen only in one of these cases should be done before
 * the request is sent. For instance:
 * - when the editor asks for a command to be performed, it should clear it from
 *   the unlocked area, as this does not happen for commands sent from the proof
 *   tree mode ;
 * - that's all I can think of right now...
 */

function editorOnRequestTriggered(requestType, request) {
    switch (requestType) {
    case 'query':
        break;
    }
}

var theoremStarters = [
    'CoFixpoint',
    'Definition',
    'Example',
    'Fixpoint',
    'Global', // Global Instance
    'Instance',
    'Lemma',
    'Theorem',
];

/*
 * TODO: OMG this is ugly, gotta make something better when I have time
 */
function splitAtFirstDelimiter(s) {
    var firstSpace = s.indexOf(' ');
    if (firstSpace === -1) { firstSpace = +Infinity; }
    var firstNewline = s.indexOf('\n');
    if (firstNewline === -1) { firstNewline = +Infinity; }
    var firstColon = s.indexOf(':');
    if (firstColon === -1) { firstColon = +Infinity; }
    var firstParen = s.indexOf('(');
    if (firstParen === -1) { firstParen = +Infinity; }
    var firstCurly = s.indexOf('{');
    if (firstCurly === -1) { firstCurly = +Infinity; }
    var firstDelimiter = Math.min(firstSpace, firstNewline, firstColon, firstParen, firstCurly);
    if (firstDelimiter === +Infinity) {
        return undefined;
    } else {
        return {
            "before": s.substring(0, firstDelimiter),
            "after": s.substring(firstDelimiter + 1),
        };
    }
}

function getVernac(s) {
    var trimmed = coqTrim(s);
    var split = splitAtFirstDelimiter(trimmed);
    if (split === undefined) {
        return s; // untrimmed!
    } else {
        return split.before;
    }
}

// TODO: extract all the constructor names from an inductive definition
// Returns the name defined by a command, if any
function getVernacName(s) {
    var trimmed = coqTrim(s);
    var split = splitAtFirstDelimiter(trimmed);
    if (split == undefined) { return undefined; }
    if (!_(theoremStarters).contains(split.before)) { return undefined; }
    split = splitAtFirstDelimiter(split.after);
    if (split == undefined) { return undefined; }
    return split.before;
}

// TODO: collect names possibly in scope here
function editorOnResponse(requestType, request, response) {
    switch (requestType) {
    case 'query':
        switch(response.rResponse.tag) {

        case 'Good':

            // activate study tactics
            if (request.indexOf("New tactics: left, right") > -1) {
                tacticsLeftRight = true;
            }
            if (request.indexOf("New tactic: apply") > -1) {
                tacticsApply = true;
            }
            if (request.indexOf("New tactic: split") > -1) {
                tacticsSplit = true;
            }
            if (request.indexOf("New tactics: cases, contradiction") > -1) {
                tacticsCasesContradiction = true;
            }
            if (request.indexOf("New tactic: simpl in *") > -1) {
                tacticsSimplInStar = true;
            }

            var rProving = mProving.find();
            var proving = doc.getRange(rProving.from, rProving.to);
            if (coqTrim(proving) !== coqTrim(request)) {
                console.log(
                    'request response was for', request,
                    'but was expecting for', proving
                );
                return;
            }
            var rProved = mProved.find();
            var nextPos = rProving.to;
            markProved(rProved.from, nextPos);
            markProving(nextPos, rProving.to);
            if (setCursorOnResponse) {
                doc.setCursor(nextPos);
            }
            updateCoqtopPane(goingDown, response);

            var name = getVernacName(request);
            if (name !== undefined) {
                if (!_(namesPossiblyInScope).contains(name)) {
                    namesPossiblyInScope.push(name);
                }
            }

            if (activeProofTree === undefined) {
                if (response.rGoals.focused.length === 1
                    && response.rGoals.unfocused.length === 0
                   ) {
                    createProofTree(response);
                }
            } else {
                // it is possible to start a proof within another proof,
                // stacking trees
                if (response.rGoals.focused.length === 1
                    && response.rGoals.unfocused.length === 0
                    && _(theoremStarters).contains(getVernac(request))
                   ) {
                    activeProofTree.div.style("display", "none");
                    activeProofTrees.push(activeProofTree);
                    createProofTree(response);
                }
            }

            break;

        case 'Fail':

            // move proving and toprove back to unlocked
            var rProving = mProving.find();
            var rProved = mProved.find();
            var rUnlocked = mUnlocked.find();
            markProving(rProving.from, rProving.from);
            markToprove(rProving.from, rProving.from);
            markUnlocked(rProving.from, rUnlocked.to);
            doc.setCursor(rProving.from);
            cm.focus(); // somehow it gets unfocused sometimes
            updateCoqtopPane(goingDown, response);

            break;
        }

        resizeCoqtopPanes();

        break;

    }
}

/*
 * Returns the result of applying [predicate] to the trimmed incoming command,
 * either in the [proving], [toprove] or [unlocked] region. If the command was
 * in [unlocked], it is also added to [toprove].
 */
function lookupRequestInIncoming(predicate) {

    var rProving = mProving.find();
    var proving = doc.getRange(rProving.from, rProving.to);

    if (proving !== "") {
        // this branch happens when one processes a lot of commands
        // [proving] should only contain one command, no need for [next]
        return predicate(coqTrim(proving));
    }

    var rToprove = mToprove.find();
    var toprove = doc.getRange(rToprove.from, rToprove.to);

    if (toprove !== "") {
        var nextIndex = next(toprove);
        var nextItem = toprove.substring(0, nextIndex);
        return predicate(nextItem);
    }

    var rUnlocked = mUnlocked.find();
    var unlocked = doc.getRange(rUnlocked.from, rUnlocked.to);
    var nextIndex = next(unlocked);
    var nextUnlocked = unlocked.substring(0, nextIndex);
    var nextPos = cm.findPosH(rUnlocked.from, nextIndex, "char");

    var result = predicate(coqTrim(nextUnlocked));

    if (!result) {
        return false;
    }

    markToprove(rToprove.from, nextPos);
    markUnlocked(nextPos, rUnlocked.to);

    return true;

}

function proofTreeQueryWish(request) {

    var requestWasPresent = lookupRequestInIncoming(function(cmd) {
        // if the query is "Proof.", we also accept things like "Proof with..."
        if (request === "Proof.") {
            return isProof(cmd);
        }
        // Abort, Defined, Qed should be interchangeable
        if (request === "Defined." || request === "Qed." || request === "Abort.") {
            return cmd === "Defined." || cmd === "Qed." || cmd === "Abort.";
        }
        return cmd === coqTrim(request);
    });

    if (!requestWasPresent) {
        var trimmed = coqTrim(request);
        switch (trimmed) {
        case '{':
        case '}':
            safePrependToprove(request);
            break;
            // for these, I want to put a newline
        case 'Qed.':
            safePrependToprove('\n' + request);
            break;
        default:
            if (isProof(trimmed)) {
                safePrependToprove('\n' + request);
                break;
            }
            safePrependToprove(request);
            //safePrependToprove('\n' + request);
            break;
        }
    }

    processToprove();

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
        } else if (sub.startsWith("*)")) {
            commentDepth--;
            pos += 2;
        } else if (commentDepth > 0) {
            pos++;
        } else {
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
        } else if (sub.startsWith("*)")) {
            commentDepth--;
            pos += 2;
        } else if (commentDepth > 0) {
            pos++;
        } else if (sub[0] === ' ' || sub[0] === '\n') {
            pos++;
        } else {
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
        } else if (sub.endsWith("(*")) {
            commentDepth--;
            pos -= 2;
        } else if (commentDepth > 0) {
            pos--;
        } else if (lastChar === ' ' || lastChar === '\n') {
            pos--;
        } else {
            return sub;
        }
    }
    return "";
}

function sameTrimmed(a, b) {
    return (coqTrim(a) === coqTrim(b));
}

function zeroPad(s) {
    return s < 10 ? '0' + s : s;
}

function getFormattedDate() {
    var d = new Date();
    var month = zeroPad(d.getMonth() + 1);
    var day = zeroPad(d.getDate());
    var hours = zeroPad(d.getHours());
    var minutes = zeroPad(d.getMinutes());
    var seconds = zeroPad(d.getSeconds());
    return d.getFullYear() + '-' + month + '-' + day + '-'
        + hours + ':' + minutes + ':' + seconds + ':' + d.getMilliseconds();
}

function captureDiffs() {
    var rUnlocked = mUnlocked.find();
    var unlocked = doc.getRange(rUnlocked.from, rUnlocked.to);
    if (coqTrimLeft(unlocked).length === 0
        //|| activeProofTree === undefined
       ) {
        return Promise.resolve();
    }
    return (
        onCtrlDown(true)
            .then(delayPromise(3 * animationDuration))
            .then(function() {
                if (activeProofTree !== undefined
                    && activeProofTree.curNode.getViewChildren().length > 0
                    && activeProofTree.curNode.getViewGrandChildren().length > 0
                   ) {
                    $("#save-screenshot").attr("download", getFormattedDate());
                    $("#screenshot-button").click();
                }
            })
            .then(captureDiffs)
    );
}

/*
  svg_todataurl will try to binary64-encode the code in the HTML using
  window.btoa, which does not deal well with things outside of Latin-1
  by default. We override these to handle Unicode.
*/

(function() {
    var old = window.btoa;
    window.btoa = function utf8_to_b64(str) {
        return old(unescape(encodeURIComponent(str)));
    }
})();

(function() {
    var old = window.atob;
    window.atob = function b64_to_utf8(str) {
        return decodeURIComponent(escape(old(str)));
    }
})();

function recordDiff() {
    if (activeProofTree) {
        window.copy(JSON.stringify({
            "before": activeProofTree.curNode.response,
            "tactic": activeProofTree.curNode.children[0].getFocusedTactic().tactic,
            "after": activeProofTree.curNode.children[0].children[0].response,
        }));
    }
}
