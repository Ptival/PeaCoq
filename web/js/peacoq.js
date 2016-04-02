requirejs.config({
  baseUrl: "js/lib",
  paths: {
    ace: "./ace",
    "peacoq-js": "../peacoq-js",
    "peacoq-ts": "../peacoq-ts",
  },
  shim: {
    "bootstrap": { deps: ["jquery"] },
    "jquery.hotkeys": { deps: ["jquery"] },
    "MathJax-master/MathJax": { deps: ["jquery"] },
    "peacoq-ts": { deps: ["peacoq-ts/utils"] },
    "w2ui/w2ui": { deps: ["jquery"] },
  },
  waitSeconds: 0,
});

// Start the main app logic.
requirejs([
    "ace/ace",
    "d3",
    "jquery",
    //"jquery-ui/jquery-ui",
    "jquery.hotkeys",
    "bootstrap",
    "jss",
    "lodash",
    "MathJax-master/MathJax",
    "rx.all",
    "tsmonad",
    "w2ui/w2ui",
  ],
  function(ace, d3, $) {
    window.ace = ace;
    // not sure how else this is usually done
    aceRequires = [
      ace.require("ace/anchor"),
      ace.require("ace/range"),
    ];
    window.AceAjax = $.extend({}, ...aceRequires);
    requirejs([
      "ace/mode/ocaml",
      "peacoq-js/highlight-coq",
      "peacoq-js/mode-coq",
      "peacoq-ts/coq-string-utils",
      "peacoq-ts/setup",
      "peacoq-ts/utils",
    ], function() {
    });
  });
