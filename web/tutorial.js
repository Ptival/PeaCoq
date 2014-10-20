
var scrollbarWidth = 20; // arbitrary
var spacing = 20;
var accordionWidth = 200;

var menu =
    [
        {
            "title": "CPDT rip-off",
            "items":
            [
                {
                    "name": "Stack Machine",
                    "setup": stackMachine,
                },
                {
                    "name": "Booleans",
                    "setup": firstStepsBooleans,
                },
            ]
        },
    ]
;

function mkText(t) { return $("<div>").text(t); }

function mkCoq(t) { return mkClickableTextarea(t, function() { }) }

function stackMachine(add) {

    add(mkText("'sup?"));

    add(mkCoq("Inductive binop : Type := Plus | Times."));

    add(mkCoq(
        'Inductive exp : Set :='
            + '\n| Const : nat -> exp'
            + '\n| Binop : binop -> exp -> exp -> exp'
            + '\n.'
    ));

    add(mkCoq(
        'Definition binopDenote (b : binop) : nat -> nat -> nat :='
            + '\n  match b with'
            + '\n  | Plus => plus'
            + '\n  | Times => mult'
            + '\nend.'
    ));

    add(mkCoq(
        'Fixpoint expDenote (e : exp) : nat :='
        + '\n  match e with'
            + '\n  | Const n => n'
            + '\n  | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)'
        + '\n  end.'
    ));

    add(mkCoq(
        "Eval simpl in expDenote (Const 42)."
    ));

    add(mkCoq(
        "Eval simpl in expDenote (Binop Plus (Const 2) (Const 2))."
    ));

    add(mkCoq(
        "Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))."
    ));

    add(mkCoq(
        "Inductive instr : Set :="
            + "\n| iConst : nat -> instr"
            + "\n| iBinop : binop -> instr"
            + "\n."
    ));

    add(mkCoq(
        "Definition prog := list instr."
    ));

    add(mkCoq(
        "Definition stack := list nat."
    ));

    add(mkCoq(
        "Definition instrDenote (i : instr) (s : stack) : option stack :="
            + "\n  match i with"
            + "\n  | iConst n => Some (n :: s)"
            + "\n  | iBinop b =>"
            + "\n    match s with"
            + "\n    | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')"
            + "\n    | _ => None"
            + "\n    end"
            + "\n  end."
    ));

    add(mkCoq(
        "Fixpoint progDenote (p : prog) (s : stack) : option stack :="
            + "\n  match p with"
            + "\n    | nil => Some s"
            + "\n    | i :: p' =>"
            + "\n      match instrDenote i s with"
            + "\n        | None => None"
            + "\n        | Some s' => progDenote p' s'"
            + "\n      end"
            + "\n  end."
    ));

    add(mkCoq(
        "Fixpoint compile (e : exp) : prog :="
            + "\n  match e with"
            + "\n    | Const n => iConst n :: nil"
            + "\n    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil"
            + "\n  end."
    ));

    add(mkCoq(
        "Eval simpl in compile (Const 42)."
    ));

    add(mkCoq(
        "Eval simpl in compile (Binop Plus (Const 2) (Const 2))."
    ));

    add(mkCoq(
        "Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))."
    ));

    add(mkCoq(
        "Eval simpl in progDenote (compile (Const 42)) nil."
    ));

    add(mkCoq(
        "Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil."
    ));

    add(mkCoq(
        "Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7))) nil."
    ));

    add(mkCoq(
        ""
    ));

    add(mkCoq(
        ""
    ));

    add(mkCoq(
        ""
    ));

    add(mkCoq(
        ""
    ));

    add(mkCoq(
        ""
    ));

}

$(document).ready(function() {

    $("#accordion")
        .css("width", accordionWidth)
    ;

    $("#main")
        .css("width", $(window).width() - accordionWidth - scrollbarWidth - spacing)
        .css("margin-left", spacing + "px")
    ;

    populateMenu();

    resetCoq();

    PT.handleKeyboard();

    // for faster debugging
    $("li > a").first().click();

});

function slugg(t) {
    var res =
        t
        .replace(/\s/g, '-')
        .toLowerCase()
    ;
    return res;
}

function mkPanel(title, item) {

    var panel =
        $("<div>")
        .addClass("panel")
        .addClass("panel-primary")
        .css("display", "none")
    ;

    panel.append(
        $("<div>")
            .addClass("panel-heading")
            .html(
                title
                    + nbsp
                    + mkGlyph("chevron-right").get(0).outerHTML
                    + nbsp
                    + item.name)
    );

    $("#main")
        .append(panel)
    ;

    var panelGroup = $("<ul>").addClass("list-group");

    panel.append(panelGroup);

    var buttonToAddLinesContainer =
        $("<li>")
        .addClass("list-group-item")
        .append(
            $("<button>")
                .addClass("label")
                .addClass("label-primary")
                .append(mkGlyph("plus"))
                .click(function() {
                    $(this).parent().before(
                        $("<li>")
                            .addClass("list-group-item")
                            .append(
                                mkClickableTextarea("")
                            )
                    );
                })
        )
    ;

    panelGroup.append(buttonToAddLinesContainer);

    item.setup(function(item) {
        buttonToAddLinesContainer.before(
            $("<li>").addClass("list-group-item").append(item)
        );
    });

    return panel;

}

function populateMenu() {
    var group = $("#accordion");
    _(menu).each(function(e, ndx) {
        var title = e.title;
        var slug = slugg(title);

        var items = _(e.items).map(function(i) {
            var thisPanel = mkPanel(title, i);
            return $("<li>")
                .append($('<a href="#">').text(i.name).click(function() {
                    $("#main > .panel").css("display", "none");
                    thisPanel.css("display", "");
                    $("textarea").change();
                }))
            ;
        });

        var panel = $("<div>")
            .addClass("panel")
            .html(
                '<div class="panel-heading">'
                    + '<a class="collapsed" data-toggle="collapse"'
                    + ' data-parent="#accordion" href="#' + slug + '">'
                    + '<h1 class="panel-title">'
                    + title
                    + '</h4></a></div>'
                    + '<div id="' + slug + '" class="panel-collapse collapse'
                    + (ndx == 0 ? ' in' : '')
                    + '">'
                    + '<div class="accordion-body">'
                    + '</div></div>'
            )
        ;
        group.append(panel);
        var itemContainer = panel.find(".accordion-body");
        _(items).each(function(i) {
            itemContainer.append(i);
        });
    });
}

function firstStepsBooleans(addItem) {

    addItem(
        $("<div>")
            .text("Here is our first Coq definition, the inductive type bool:")
    );

    addItem(mkClickableTextarea(inductiveBool, function() { }));

    addItem(
        $("<div>")
            .text("Here is a provable thingy:")
    );

    addItem(mkClickableTextarea(
        "Theorem trivial : forall b : bool, b = false \\/ b = true."
        , function() { }));

    addItem(
        $("<div>")
            .text("This one doesn't belong here, but testing is easier this way!")
    );

    addItem(mkClickableTextarea(inductiveNat, function() { }));

}

function mkClickableTextarea(initialText) {
    var res = $("<div>").addClass("input-group");
    res.append(
        $("<textarea>")
            .addClass("form-control")
            .addClass("resizeHeight")
            .val(initialText)
    );
    res.append(
        $("<span>")
            .addClass("input-group-btn")
            .append(mkPlayButton(function() {
                var li = $(this).parents("li").first();
                var query = li.find("textarea").val();

                // remove the previous alert, if any
                li.find("div.alert").remove();

                if (query.startsWith("Inductive")) {

                    syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            syncParse(query, function(response) {
                                var answer =
                                    $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(showVernac(response))
                                ;
                                li.append(answer);
                                $("body").animate({
                                        "scrollTop": li.offset().top,
                                }, 1000);
                            });
                            break;

                        case "Fail":
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-danger")
                                    .css("font-family", "monospace")
                                    .html(response.rResponse.contents)
                            );
                            break;

                        default:
                            alert("TODO");
                            break;

                        };

                    });

                } else if (query.startsWith("Theorem")) {

                    var anchor = $("<div>");

                    li.append(anchor);

                    var pt = new ProofTree(
                        d3.select(anchor.get(0)),
                        anchor.width(),
                        400,
                        function(prooftree) {

                            var prettyTheorem;
                            syncParse(prooftree.theorem, function(response) {
                                prettyTheorem = showVernac(response);
                            });

                            prooftree.replay();
                            prooftree.qed();
                            anchor.empty();
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(
                                        prettyTheorem
                                            + "<br>" + vernac("Proof") + syntax(".") + "<br>"
                                            + PT.pprint(prooftree.proof(), 1)
                                            + "<br>" + vernac("Qed") + syntax(".")
                                    )
                            );
                        },
                        undefined,
                        function(prooftree, error) {
                            prooftree.svg.style("display", "none");
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-danger")
                                    .css("font-family", "monospace")
                                    .html(error)
                            );
                        }
                    );

                    anchor.click(function() {
                        makeActive(pt);
                    });

                    pt.newTheorem(query, PT.tDiscriminate, function() { }, function() { });

                } else if (query.startsWith("Definition")) {

                    syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            syncParse(query, function(response) {
                                var answer =
                                    $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(showVernac(response))
                                ;
                                li.append(answer);
                                $("body").animate({
                                        "scrollTop": li.offset().top,
                                }, 1000);
                            });
                            break;

                        case "Fail":
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-danger")
                                    .css("font-family", "monospace")
                                    .html(response.rResponse.contents)
                            );
                            break;

                        default:
                            alert("TODO");
                            break;

                        };

                    });

                } else if (query.startsWith("Fixpoint")) {

                    syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            syncParse(query, function(response) {
                                var answer =
                                    $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-success")
                                    .css("font-family", "monospace")
                                    .html(showVernac(response))
                                ;
                                li.append(answer);
                                $("body").animate({
                                        "scrollTop": li.offset().top,
                                }, 1000);
                            });
                            break;

                        case "Fail":
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-danger")
                                    .css("font-family", "monospace")
                                    .html(response.rResponse.contents)
                            );
                            break;

                        default:
                            alert("TODO");
                            break;

                        };

                    });

                } else if (query.startsWith("Eval")) {

                    syncQuery(query, function(response) {

                        switch (response.rResponse.tag) {

                        case "Good":
                            var response = stripWarning(response.rResponse.contents[0]);
                            syncParseEval(response, function(response) {
                                var value = response[0];
                                var type = response[1];
                                li.append(
                                    $("<div>")
                                        .addClass("alert")
                                        .addClass("alert-success")
                                        .css("font-family", "monospace")
                                        .html(
                                            syntax("=") + nbsp + showTerm(value)
                                                + "<br>" + syntax(":") + nbsp + showTerm(type)
                                        )
                                );
                            });
                            break;

                        case "Fail":
                            li.append(
                                $("<div>")
                                    .addClass("alert")
                                    .addClass("alert-danger")
                                    .css("font-family", "monospace")
                                    .html(response.rResponse.contents)
                            );
                            break;

                        default:
                            alert("TODO");
                            break;

                        };

                    });

                } else {
                    alert("This type of query is not supported yet.");
                }

/*
                syncParse(text, function(response) {
                    li.find("div.alert").remove();
                    li.append(
                        $("<div>")
                            .addClass("alert")
                            .addClass("alert-success")
                            .css("font-family", "monospace")
                            .html(showVernac(response))
                    );
                });
*/

            }))
    );
    return res;
}

function mkGlyph(name) {
    return $("<i>").addClass("glyphicon").addClass("glyphicon-" + name);
}

function mkPlayButton(onClick) {
    var res = $("<button>")
        .addClass("btn btn-default")
        .attr("type", "button")
        .append(mkGlyph("play"))
    ;
    res.click(onClick);
    return res;
}

var inductiveBool =
  'Inductive bool : Type :=\n'
+ '| true : bool\n'
+ '| false : bool\n'
+ '.'
;

var inductiveNat =
  'Inductive nat : Type :=\n'
+ '| O : nat\n'
+ '| S : nat -> nat\n'
+ '.'
;

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

function syncQueryUndo(q, h) { syncRequest('queryundo', q, h); }

function syncParse(q, h) { syncRequest('parse', q, h); }

function syncParseEval(q, h) { syncRequest('parseEval', q, h); }

function currentLabel() {
    var result;
    syncRequest("status", "", function(response) {
        var msg = response.rResponse.contents[0];
        result = msg.match("^.*,.*,.*,\"(.*)\",.*$")[1];
    });
    return + result;
}

function resetCoq() {
    var label = currentLabel();
    if (label > 1) {
        syncRequest("rewind", label - 1, function() { });
        syncQuery("Require Import Unicode.Utf8 Bool Arith List.", function() { });
        syncQuery("Open ListNotations.", function() { });
    }
}

if (!String.prototype.startsWith) {
  Object.defineProperty(String.prototype, 'startsWith', {
    enumerable: false,
    configurable: false,
    writable: false,
    value: function (searchString, position) {
      position = position || 0;
      return this.lastIndexOf(searchString, position) === position;
    }
  });
}

function stripWarning(s) { return s.substring(s.indexOf('\n') + 1); }

function nl2br (str) {
    return (str + '').replace(/([^>\r\n]?)(\r\n|\n\r|\r|\n)/g, '$1<br>$2');
}
