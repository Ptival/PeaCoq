
$(document).ready(function() {

    includeLodash();

    setupTextareaResizing();

    resetCoq();

    separateCode();

    makeCodeInteractive();

});

function includeLodash() {

    $("head")
        .append(
            $("<script>")
                .attr("type", "text/javascript")
                .attr("src", "lodash.js")
        )
    ;

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
        printResponse(response);
        var msg = response.rResponse.contents[0];
        result = msg.match("^.*,.*,.*,\"(.*)\",.*$")[1];
    });
    return + result;
}

function resetCoq() {
    var label = currentLabel();
    if (label > 1) {
        syncRequest("rewind", label - 1, printResponse);
        syncQuery("Require Import Unicode.Utf8.", printResponse);
    }
}

function separateCode() {

    var commands = [
        "Definition",
        "Inductive",
        "Example",
        "Check",
        "Eval",
        "Notation",
    ];

    $(".code")
        .replaceWith(function() {

            var result = $("<div>").append($('<div class="code">').css("clear", "left"));

            var reduceResult =
                _.reduce(
                    $(this).contents(),
                    function(acc, elt){
                        if (_(commands).contains($(elt).text())) {
                            acc.append($('<div class="code">').css("clear", "left").append(elt));
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

    $(".code")
    // keep the ones that seem to contain code to run
        .filter(function() { var t = $(this).text(); return t.indexOf('.') > 0; })
        .each(function() {

            var html = $(this).html();
            $(this).empty();

            $(this).append($("<div>").html(html).addClass("right"));

            var clickyDiv = $("<div>")
                //.html("<br>")
                .addClass("left")
            ;
            $(this).append(clickyDiv);

            var clicky = $("<div>").addClass("clicky");
            resetClicky.call(clicky);
            clickyDiv.append(clicky);
        })
    ;

    var clickyWidth = "30px";

    /*** holy grailing it up ***/
    $(".doc").css("clear", "left");

    $(".code")
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

    /*** roosterizing it up ***/
    $(".code >> span.id:contains(admit)")
        .replaceWith('<textarea>')
    ;
    $("textarea").parent().parent().append(
        $('<div class="error"></div>')
            .css("position", "relative")
            .css("float", "left")
    );
    $('.code >> span.comment:contains("FILL")').remove();
    $('.code >> span.comment:contains("==>")').remove();
    $(".code").append(
        $('<div class="response">')
            .css("position", "relative")
            .css("float", "left")
    );

}

function backtrack(toLabel) {
    var fromLabel = currentLabel();
    syncRequest("rewind", fromLabel - toLabel, printResponse);
    $(".clicky")
        .filter(function() {
            var label = $(this).data("label");
            return label !== undefined && label >= toLabel;
        })
        .each(resetClicky)
    ;
}

function resetClicky() {
    $(this)
        .html("▸")
        .css("background-color", "orange")
        .off("click")
        .click(_.partial(onClick, $(this)))
    ;
    $(this).parent().parent().find(".response").empty();
}

function onClick(clicky) {

    var label = currentLabel();

    var queriesDiv = $(this).parent().parent().children(".right");

    var queries = textify(queriesDiv)
        .replace(/^\s\s*/, '') // remove heading whitespaces
        .replace(/\s\s*$/, '') // remove trailing whitespaces
        .replace(/ /g, ' ') // replace tabulations with spaces
        .replace(/⇒/g, '=>')
    ;

    var responseDiv = clicky.parent().parent().find(".response");
    responseDiv.empty();

    var allGood = true;

    var handler = function(response) {

        printResponse(response);

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
            clicky
                .css("background-color", "red")
            ;
            var msg = response.rResponse.contents;
            responseDiv
                .css("background-color", "salmon")
                .text(removeWarning(msg))
            ;
            clicky.text("✗");
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

    if (allGood) {
        clicky
            .css("background-color", "lightgreen")
            .data("label", label)
            .text("✓")
            .off("click")
            .on("click", _.partial(backtrack, label))
        ;
    }

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
    syncQuery(q, printResponse);
}

function printResponse(response) {
    console.log("tag:", response.rResponse.tag,
                "contents:", response.rResponse.contents);
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
