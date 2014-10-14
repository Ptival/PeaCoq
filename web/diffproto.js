
function avg(n1, n2) { return (n1 + n2) / 2; }

function mkDot(x, y) { return {"x": x, "y": y}; }

function showDot(d) { return d.x + " " + d.y; }

function midDot(d1, d2) { return mkDot(avg(d1.x, d2.x), avg(d1.y, d2.y)); }

function shiftLeft(d, n) { return mkDot(d.x - n, d.y); }
function shiftRight(d, n) { return mkDot(d.x + n, d.y); }

function connectRects(r1, r2) {
    var a = mkDot(r1.left, r1.top);
    var b = mkDot(r1.right, r1.top);
    var c = mkDot(r2.left, r2.top);
    var d = mkDot(r2.right, r2.top);
    var e = mkDot(r2.right, r2.bottom);
    var f = mkDot(r2.left, r2.bottom);
    var g = mkDot(r1.right, r1.bottom);
    var h = mkDot(r1.left, r1.bottom);

    var cp1 = mkDot(avg(b.x, c.x), b.y);
    var cp2 = mkDot(avg(f.x, g.x), c.y);
    var cp3 = mkDot(avg(f.x, g.x), f.y);
    var cp4 = mkDot(avg(f.x, g.x), g.y);

    return (
        "M" + showDot(a)
            + "L" + showDot(b)
            + "C" + showDot(cp1) + "," + showDot(cp2) + "," + showDot(c)
            + "L" + showDot(d) + "," + showDot(e) + "," + showDot(f)
            + "C" + showDot(cp3) + "," + showDot(cp4) + "," + showDot(g)
            + "L" + showDot(h)
            + "Z"
    );

}

var opacity = 1;
var green = "#C1FFC1";
var blue = "#CCDDEE";

$(document).ready(function() {

    var d = [];
    d[0] = $("#d0")[0].getBoundingClientRect();
    d[1] = $("#d1")[0].getBoundingClientRect();
    d[2] = $("#d2")[0].getBoundingClientRect();
    d[3] = $("#d3")[0].getBoundingClientRect();
    d[4] = $("#d4")[0].getBoundingClientRect();
    d[5] = $("#d5")[0].getBoundingClientRect();
    d[6] = $("#d6")[0].getBoundingClientRect();
    d[7] = $("#d7")[0].getBoundingClientRect();

    var delta = 2;

    var g1TopRightStart =
        {"top": d[2].top, "right": d[2].right, "bottom": d[2].top + delta, "left": d[2].left};
    var leftEnd =
        {"top": d[1].bottom - delta, "right": d[1].right, "bottom": d[1].bottom, "left": d[1].left};
    var g3TopRightStart =
        {"top": d[6].top, "right": d[6].right, "bottom": d[6].top + delta, "left": d[6].left};

    var n1diff = d3.select("#diff-layer").append("g").style("opacity", 0);
    var n2diff = d3.select("#diff-layer").append("g").style("opacity", 0);
    var n3diff = d3.select("#diff-layer").append("g").style("opacity", 0);

    n1diff
        .append("path")
        .attr("fill", green)
        .attr("opacity", opacity)
        .attr("d", connectRects(d[0], g1TopRightStart))
    ;

    n1diff
        .append("path")
        .attr("fill", "transparent")
        .attr("opacity", opacity)
        .attr("d", connectRects(d[1], d[2]))
    ;

    n1diff
        .append("path")
        .attr("fill", green)
        .attr("opacity", opacity)
        .attr("d", connectRects(leftEnd, d[3]))
    ;

    n2diff
        .append("path")
        .attr("fill", "transparent")
        .attr("opacity", opacity)
        .attr("d", connectRects(d[0], d[4]))
    ;

    n2diff
        .append("path")
        .attr("fill", blue)
        .attr("opacity", opacity)
        .attr("d", connectRects(d[1], d[5]))
    ;

    n3diff
        .append("path")
        .attr("fill", green)
        .attr("opacity", opacity)
        .attr("d", connectRects(d[0], g3TopRightStart))
    ;

    n3diff
        .append("path")
        .attr("fill", green)
        .attr("opacity", opacity)
        .attr("d", connectRects(leftEnd, d[7]))
    ;

    d3.select("#g1")
        .on("mouseover", function() {
            n1diff.style("opacity", 1);
        })
        .on("mouseout", function() {
            n1diff.style("opacity", 0);
        })
    ;

    d3.select("#g2")
        .on("mouseover", function() {
            n2diff.style("opacity", 1);
        })
        .on("mouseout", function() {
            n2diff.style("opacity", 0);
        })
    ;

    d3.select("#g3")
        .on("mouseover", function() {
            n3diff.style("opacity", 1);
        })
        .on("mouseout", function() {
            n3diff.style("opacity", 0);
        })
    ;

});
