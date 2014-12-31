
var nextVector = [
    ["", 0],
    [".", 1],
    ["...", 3],
    ["Theorem t {x : A.t} : y.", 24],
    ["{A : t}", 0],
    ["{A . t}", 1],
    ["\n {A . t}", 3],
    ["(* Trap. *) Definition foo {T : Type} : T.", 42],
];

$(document).ready(function() {

    var margin = 2;
    var padding = 4;

    $("body")
        .css("font-family", "monospace")
    ;

    _(nextVector).each(function(pair) {
        var input = pair[0], expected = pair[1];
        var output = next(input);
        if (output === expected) {
            $("<div>", {
                "class": "alert alert-success",
                "html":
                "✓ next(\"" + input + "\")",
            })
                .css("margin", margin)
                .css("padding", padding)
                .appendTo("body")
            ;
        } else {
            $("<div>", {
                "class": "alert alert-danger",
                "html":
                "✗ next(\"" + input + "\")<br/>Expected: " + expected + "<br/>Obtained: " + output,
            })
                .css("margin", margin)
                .css("padding", padding)
                .appendTo("body")
            ;
        }
    });

});
