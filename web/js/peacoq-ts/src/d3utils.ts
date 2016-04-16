import * as d3 from 'd3';

let diffColor = (function() {
  let colors = [
    "#ffbb78",
    "#f7b6d2",
    "#dbdb8d",
    "#6b6ecf",
    "#8ca252",
    "#b5cf6b",
    "#cedb9c",
    "#bd9e39",
    "#d6616b",
    "#ce6dbd",
    "#de9ed6",
  ];
  let scale = d3.scale.ordinal().range(colors);
  return function(n) {
    return scale(n);
  };
})();
