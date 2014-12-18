
$(document).ready(function() {

    PT.resetCoq();

    PT.handleKeyboard();

    var scrollbarWidth = 20; // arbitrary

    var pt = new ProofTree(
        d3.select("body"),
        $(window).width() - scrollbarWidth,
        $(window).height(),
        function(){}
    );

    makeActive(pt);

    var times = [];

    var n = 0;

    var bound = 30;

    function proceed() {
        var before = new Date();
        pt.click(
            pt.curNode.children[0],
            false,
            function() {
                var after = new Date();
                times.push(after - before);
                n++;
                if (n < bound) {
                    window.setTimeout(proceed, 1000);
                } else {
                    console.log(times);
                }
            }
        );
    }

    pt.newTheorem(
        "Theorem stress : False.",
        function(pt) { return ["pose proof I"]; },
        function(){},
        function(){ console.log("proceeding"); proceed(); }
    );

});
