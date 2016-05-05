requirejs.config({
  paths: {
    "ace": "../node_modules/ace-code-editor/lib/ace",
    "bootstrap": "../node_modules/bootstrap/dist/js/bootstrap",
    "d3": "../node_modules/d3/d3",
    "jquery": "../node_modules/jquery/dist/jquery",
    "jquery.hotkeys": "../node_modules/jquery.hotkeys/jquery.hotkeys",
    "jss": "../node_modules/jss-browserify/jss",
    "lodash": "../node_modules/lodash/lodash",
    "MathJax": "../node_modules/mathjax/MathJax",
    "rx": "../node_modules/rx/dist/rx.all",
    "tsmonad": "../node_modules/tsmonad/dist/tsmonad",
    "w2ui": "../node_modules/w2ui/w2ui",
  },
  shim: {
    "bootstrap": { deps: ["jquery"] },
    "jquery.hotkeys": { deps: ["jquery"] },
  },
  waitSeconds: 0,
});

// Start the main app logic.
requirejs([
    // need binding?
    "ace/ace",
    // don't need binding
    "bootstrap",
    "d3",
    "jquery",
    "jquery.hotkeys",
    "jss",
    "lodash",
    "MathJax",
    "rx",
    "tsmonad",
    "w2ui",
  ],
  function(ace) {
    window.ace = ace;
    // not sure how else this is usually done
    aceRequires = [
      ace.require("ace/anchor"),
      ace.require("ace/range"),
    ];
    window.AceAjax = $.extend({}, ...aceRequires);
    requirejs([
      // "ace/mode/ocaml",
      "peacoq-js/highlight-coq",
      "peacoq-js/mode-coq",
      "peacoq-js-of-ts/coq/binder-kind",
      "peacoq-js-of-ts/coq/case-style",
      "peacoq-js-of-ts/coq/feedback-content",
      "peacoq-js-of-ts/coq/local-binder",
      "peacoq-js-of-ts/coq/paren-relation",
      "peacoq-js-of-ts/coq/prim-token",
      "peacoq-js-of-ts/coq/unparsing",
      "peacoq-js-of-ts/coq/binding-kind",
      "peacoq-js-of-ts/coq/coq-constr-expr",
      "peacoq-js-of-ts/coq/feedback",
      "peacoq-js-of-ts/coq/message-level",
      "peacoq-js-of-ts/coq/ppbox",
      "peacoq-js-of-ts/coq/reference",
      "peacoq-js-of-ts/coq/value-fail",
      "peacoq-js-of-ts/coq/block-type",
      "peacoq-js-of-ts/coq/gallina",
      "peacoq-js-of-ts/coq/message",
      "peacoq-js-of-ts/coq/ppcmd-token",
      "peacoq-js-of-ts/coq/status",
      "peacoq-js-of-ts/coq/xml-tag",
      "peacoq-js-of-ts/coq/cases-pattern-expr",
      "peacoq-js-of-ts/coq/explicitation",
      "peacoq-js-of-ts/coq/glob-sort-gen",
      "peacoq-js-of-ts/coq/name-base",
      "peacoq-js-of-ts/coq/ppcut",
      "peacoq-js-of-ts/coq/str-token",
      "peacoq-js-of-ts/coq/xml-tree",
      "peacoq-js-of-ts/coq-string-utils",
      "peacoq-js-of-ts/setup",
      "peacoq-js-of-ts/utils",
    ], function() {
    });
  });
