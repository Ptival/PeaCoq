
$(document).ready(function() {

    includeLodash();

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

function resetCoq() {

    var nbStepsToRewind;
    syncRequest("status", "", function(response) {
        console.log("status", response);
        var msg = response.rResponse.contents[0];
        nbStepsToRewind = msg.match("^.*,.*,.*,\"(.*)\",.*$")[1];
    });
    syncRequest("rewind", nbStepsToRewind - 1, printResponse);
    syncQuery("Require Import Unicode.Utf8.", printResponse);

}

var commands = [
    "Definition",
    "Inductive",
    "Example",
    "Check",
    "Eval",
    "Notation",
]

function separateCode() {

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

/*
            return _.reduce(
                $(this).contents(),
                function(acc, elt){

                    console.log("elt", $(elt).text());
                    return acc.children(":last").append(elt);


                    //console.log(acc);
                    if (_(["Definition", "Inductive", "Example", "Check"]).contains($(elt).text())) {
                        return acc.append($('<div class="code">').append(elt));
                    } else {
                        return acc.children(":last").append(elt);
                    }


                },
                $("<div>").append($('<div class="code">START!</div>'))
            ).html();
*/

        })
    ;

/*
    var defFilter = "span.id:contains(Definition)";
    $(".code")
        .replaceWith(function() {
            // can't use nextUntil because it ignores text nodes
            var result = $("<div>");

            var defsHTML = $(this).html().replace(/^\s*\<br\>/, "");

            var splitPatterns = [
                "<br>\\s*<br>",
                //"42<br>\n&nbsp;&nbsp;&nbsp;.*\\(\\*.*\\*\\)",

            ];

            _(defsHTML.split(new RegExp(splitPatterns.join("|")))).each(function(e) {
                result.append($('<div class="code">').css("clear", "left").html("<br>" + e + "<br>"));
            });

            return result;
        })
    ;
*/

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

            var clicky =
                $("<div>")
                .html("▸")
                .addClass("clicky")
                .css("background-color", "orange")
            ;
            clickyDiv.append(clicky);

            clicky.click(_.partial(onClick, clicky));

        })
    ;

    var leftWidth = "30px";

    /*** holy grailing it up ***/
    $(".doc").css("clear", "left");

    $(".code")
        .css("padding-left", leftWidth)
        .css("position", "relative")
        .css("float", "left")
    ;

    $(".clicky")
        .css("font-size", "40px")
        .css("line-height", "100%")
        .css("text-align", "center")
    ;

    $(".left")
        .css("width", leftWidth)
        .css("right", leftWidth)
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
    $('.code >> span.comment:contains("FILL")').empty();
    $('.code >> span.comment:contains("==>")')
        .addClass("response")
        .empty()
    ;

}

function onClick(clicky) {

    var queriesDiv = $(this).parent().parent().children(".right");

    var queries = textify(queriesDiv)
        .replace(/^\s\s*/, '') // remove heading whitespaces
        .replace(/\s\s*$/, '') // remove trailing whitespaces
        .replace(/ /g, ' ') // replace tabulations with spaces
        .replace(/⇒/g, '=>')
    ;

    var allGood = true;

    var handler = function(response) {

        printResponse(response);

        switch(response.rResponse.tag) {

        case "Good":
            clicky
                .css("background-color", "lightgreen")
                .off("click")
            ;
            clicky.parent().parent().find(".error").empty();
            var msg = response.rResponse.contents[0];
            if (msg !== "") {
                clicky.parent().parent().find(".response")
                    .css("background-color", "lightgreen")
                    .text(removeWarning(msg))
                ;
            }
            clicky.text("✓");
            break;

        case "Fail":
            allGood = false;
            clicky
                .css("background-color", "red")
            ;
            var msg = response.rResponse.contents;
            clicky.parent().parent().find(".error")
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
    console.log(response.rResponse.tag, response.rResponse.contents);
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
