function renderSum(bottom, top, right): JQuery {
  var result = $("<span>", {
    style: "display: flex; flex-flow: row; align-items: center;"
  });
  var sum = $("<span>", {
    style: "display: flex; flex-flow: column; margin-right: 0.5em;"
  }).appendTo(result);
  $("<span>", {
    style: "display: flex; flex-flow: row; justify-content: center; background-color: #E91E63;"
  })
    .append(top)
    .appendTo(sum);
  $("<span>", {
    style: "display:flex; flex-flow: row; justify-content: center; font-family: MathJax_Size2; line-height: 1.6em;"
  })
    .text("∑")
    .appendTo(sum);
  $("<span>", {
    style: "display: flex; flex-flow: row; justify-content: center; background-color: #F44336;"
  })
    .append(bottom)
    .appendTo(sum);
  $("<span>", {
    style: "background-color: #9C27B0;"
  })
    .append(right)
    .appendTo(result);
  return result;
}

$(document).ready(function() {
  renderSum(
    $("<span>").text("let x := 42 in x"),
    $("<span>").text("y"),
    $("<span>").text("z + x")
    ).appendTo("body");

  //typeset();
});

function typeset() {
  MathJax.Hub.Queue(["Typeset", MathJax.Hub]);
}
