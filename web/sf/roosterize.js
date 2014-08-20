
var debug = false;

$(document).ready(function() {

    $('head').append('<link rel="stylesheet" href="../d3tree.css" type="text/css" />');
    includes([
        'lodash.js',
        '../d3/d3.js',
        '../prooftree.js',
    ],
    function() {

        PT.handleKeyboard();
        setupTextareaResizing();
        resetCoq();
        separateCode();
        makeCodeInteractive();

    });

});

// note the <script> tag will not show up in the DOM even though it works
function includes(paths, callback) {
    if (paths.length < 1) { callback(); }
    else {
        var fst = paths.shift();
        $.getScript(fst, function() {
            includes(paths, callback);
        });
    }
}

function setupTextareaResizing() {

    var hiddenDiv = $("<div id='invisible'>")
        .css("font-family", "monospace")
        .css("display", "none")
        .css("float", "right")
    ;

    $("body").append(hiddenDiv);

    var resizeTextarea = function() {
        content = $(this).val();
        hiddenDiv.html(
            content
                .replace(/\n/g, '&nbsp;&nbsp;<br>')
                .replace(/ /g, '&nbsp;')
                + '&nbsp;&nbsp;<br>'
        );
        $(this).css('width', Math.max(hiddenDiv.width(), 10));
        $(this).css('height', Math.max(hiddenDiv.height(), 16));
    };

    $(document)
        .on('change keyup keydown paste', 'textarea', resizeTextarea)
    ;

}

function currentLabel() {
    var result;
    syncRequest("status", "", function(response) {
        debugResponse(response);
        var msg = response.rResponse.contents[0];
        result = msg.match("^.*,.*,.*,\"(.*)\",.*$")[1];
    });
    return + result;
}

function resetCoq() {
    var label = currentLabel();
    if (label > 1) {
        syncRequest("rewind", label - 1, debugResponse);
        syncQuery("Require Import Unicode.Utf8.", debugResponse);
    }
}

function separateCode() {

    var commands = [
        "Check",
        "Definition",
        "Eval",
        "Example",
        "Fixpoint",
        "Inductive",
        "Lemma",
        "Module",
        "Notation",
        //"Proof",
        "Theorem",
    ];

    $("#main > .code")
        .replaceWith(function() {

            var result =
                $("<div>")
                .addClass("code-container")
                .append($('<div class="code">')
                .css("clear", "left"))
            ;

            var reduceResult =
                _.reduce(
                    $(this).contents(),
                    function(acc, elt){
                        if (_(commands).contains($(elt).text())) {
                            acc.append(
                                $('<div class="code">')
                                    .css("clear", "left").append(elt)
                            );
                        } else {
                            acc.children(":last").append(elt);
                        }
                        return acc;
                    },
                    result
            );

            return result;

        })
    ;

}

function makeCodeInteractive() {

    $(".code-container > .code")
    // keep the ones that seem to contain code to run
        .filter(function() { var t = $(this).text(); return t.indexOf('.') > 0; })
        .each(function() {

            var admittedSpan = $(this).find("span:contains(Admitted)");

            if (admittedSpan.size() > 0) {

                // replace the Admitted with a proof tree placeholder

                var ptDiv = $("<div>").addClass("anchor");

                $(this).contents()
                    .slice(
                        $(this).contents().index($(this).find(".comment"))
                    )
                    .replaceWith(ptDiv)
                ;

                var theorem = textify(
                    $(this).contents()
                );

                var pt = new PT.ProofTree(
                    d3.selectAll(ptDiv.toArray()),
                    1000, 400,
                    function() {
                        pt.replay();
                        pt.qed();
                        pt.svg.style("display", "none");
                        pt.proof
                            .style("display", "")
                            .html(
                                "Proof.<br>"
                                    + PT.pprint(PT.proof(pt.rootNode), 1)
                                    + "Qed."
                            )
                        ;
                    },
                    ".."
                );

                new Clicky(
                    $(this),
                    function(clicky) {
                        return pt.newTheorem(
                            theorem,
                            PT.tSet,
                            function() {
                                clicky.label = currentLabel();
                                pt.click(pt.rootNode);
                            }
                        );
                    },
                    function() {
                        pt.svg.style("display", "none");
                        pt.proof.style("display", "none");
                        pt.error.style("display", "none");
                    }
                );

            } else {

                if ($(this).find("span:contains(admit)").size() > 0) {

                    // replace the admit with a textarea
                    $(this).children()
                        .slice(
                            $(this).find(".comment").index(),
                            $(this).find("span:contains(admit)").index() + 1
                        )
                        .replaceWith($("<textarea>").text("(* FILL IN HERE *)"))
                    ;

                }

                new Clicky($(this), onClickDefinition);

            }
        })
    ;

    var clickyWidth = "30px";

    /*** holy grailing it up ***/
    $(".doc").css("clear", "left");

    $(".code-container > .code")
        .css("padding-left", clickyWidth)
        .css("position", "relative")
        .css("float", "left")
    ;

    $(".clicky")
        .css("font-size", "40px")
        .css("line-height", "100%")
        .css("text-align", "center")
    ;

    $(".left")
        .css("width", clickyWidth)
        .css("right", clickyWidth)
        .css("margin-left", "-100%")
        .css("position", "relative")
        .css("float", "left")
    ;

    $(".right")
        .css("width", "100%")
        .css("position", "relative")
        .css("float", "left")
    ;

    $("textarea").parent().parent().append(
        $('<div class="error"></div>')
            .css("position", "relative")
            .css("float", "left")
    );
    $('.code-container > .code >> span.comment:contains("==>")').remove();
    $(".code-container > .code").append(
        $('<div class="response">')
            .css("position", "relative")
            .css("float", "left")
    );

}

function onClickDefinition(clicky) {

    clicky.label = currentLabel();

    var queriesDiv = clicky.div.parent().parent().children(".right");

    var queries = textify(queriesDiv)
        .replace(/^\s\s*/, '') // remove heading whitespaces
        .replace(/\s\s*$/, '') // remove trailing whitespaces
        .replace(/ /g, ' ') // replace tabulations with spaces
        .replace(/⇒/g, '=>')
    ;

    var responseDiv = clicky.div.parent().parent().find(".response");
    responseDiv.empty();

    var allGood = true;

    var handler = function(response) {

        debugResponse(response);

        switch(response.rResponse.tag) {

        case "Good":
            var msg = response.rResponse.contents[0];
            if (msg !== "") {
                responseDiv
                    .css("background-color", "lightgreen")
                    .text(removeWarning(msg))
                ;
            }
            break;

        case "Fail":
            allGood = false;

            var msg = response.rResponse.contents;
            responseDiv
                .css("background-color", "salmon")
                .text(removeWarning(msg))
            ;
            clicky.div.text("✗");
            break;

        default:
            alert("unexpected response tag:" + response.rResponse.tag);

        };

    }

    _(queries.split(/\.\s*/))
        .each(function(query) {
            // remove comments of the form (* ... *)
            query = query.replace(/\(\*.*\*\)/g, "");
            if (allGood && /\S/.test(query)) {
                syncQuery(query + ".", handler);
            }
        })
    ;

    return allGood;

}

function syncRequest(r, q, h) {
    if (r === 'query') { console.log(q); }
    $.ajax({
        type: 'POST',
        url: '/' + r,
        data: {query : q},
        async: false,
        success: h,
    });
}

function syncQuery(q, h) { syncRequest('query', q, h); }

function syncQueryUndo(q, h) { syncRequest('queryundo', q, h); }

function debugQuery(q) {
    syncQuery(q, debugResponse);
}

function debugResponse(response) {
    if (debug) {
        console.log("tag:", response.rResponse.tag,
                    "contents:", response.rResponse.contents);
    }
}

function textify(div) {
    $(div).find("textarea").replaceWith(function() {
        return '<span class="textarea">' + $(this).val() + "</span>";
    });
    var result = $(div).text();
    $(div).find(".textarea").replaceWith(function() {
        return "<textarea>" + $(this).text() + "</textarea>";
    });
    return result;
}

function removeWarning(msg) {
    return msg.substring(msg.indexOf("\n"));
}

function scrollTo(element) {
    $('html, body').animate({
        scrollTop: element.offset().top,
    }, 2000);
}

/*
Clickies are buttons with the following properties:
- they insert themselves to the left of their anchor
- upon being clicked, they run onClick and turn:
  - green if onClick returns true, and become cancellable when clicked
  - red if onClick returns false, but can be reclicked to retry onClick
- cancelling a clicky cancels all the clicky having successed later than it
- a cancelled clicky resets itself to a clickable clicky
*/
function Clicky(anchor, onClick, onReset) {

    this.anchor = anchor;
    this.onClick = onClick;
    this.onReset = onReset;

    var right = $("<div>").addClass("right");
    anchor.contents().wrapAll(right);
    var left = $("<div>").addClass("left");
    anchor.append(left);

    this.div = $("<div>")
        .addClass("clicky")
        .data("clicky", this)
    ;
    this.reset();
    left.append(this.div);

}

Clicky.prototype.reset = function() {

    var self = this;

    if (this.onReset !== undefined) {
        this.onReset(this);
    }

    this.div
        .html("▸")
        .css("background-color", "orange")
        .off("click")
        .click(function() {
            if (self.onClick(self)) {
                self.div
                    .css("background-color", "lightgreen")
                    .text("✓")
                    .off("click")
                    .on("click", self.backtrack.bind(self))
                ;
            } else {
                self.div
                    .css("background-color", "red")
                ;
            };
        })
    ;

    this.div.parent().parent().find(".response").empty();

}

Clicky.prototype.backtrack = function() {

    var fromLabel = currentLabel();

    var toLabel = this.label;

    syncRequest("rewind", fromLabel - toLabel, debugResponse);

    $(".clicky")
        .filter(function() {
            var label = $(this).data("clicky").label;
            return label !== undefined && label >= toLabel;
        })
        .each(function() {
            var clicky = $(this).data("clicky");
            clicky.reset.call(clicky);
        })
    ;

}