requirejs.config({
  paths: {
    "ace": "../bower_components/ace/lib/ace",
    "bootstrap": "../bower_components/bootstrap/dist/js/bootstrap",
    "d3": "../bower_components/d3/d3",
    "jquery": "../bower_components/jquery/dist/jquery",
    "jquery.hotkeys": "../bower_components/jQuery.Hotkeys/jquery.hotkeys",
    "jss": "../bower_components/jss/jss",
    "lodash": "../bower_components/lodash/lodash",
    "MathJax": "../bower_components/MathJax/MathJax",
    "rx.all": "../bower_components/rxjs/dist/rx.all",
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
    "ace/ace",
    "d3",
    "jquery",
    "jquery.hotkeys",
    "bootstrap",
    "jss",
    "lodash",
    "MathJax",
    "rx.all",
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
      "peacoq-ts/coq/binder-kind",
      "peacoq-ts/coq/case-style",
      "peacoq-ts/coq/feedback-content",
      "peacoq-ts/coq/local-binder",
      "peacoq-ts/coq/paren-relation",
      "peacoq-ts/coq/prim-token",
      "peacoq-ts/coq/unparsing",
      "peacoq-ts/coq/binding-kind",
      "peacoq-ts/coq/coq-constr-expr",
      "peacoq-ts/coq/feedback",
      "peacoq-ts/coq/message-level",
      "peacoq-ts/coq/ppbox",
      "peacoq-ts/coq/reference",
      "peacoq-ts/coq/value-fail",
      "peacoq-ts/coq/block-type",
      "peacoq-ts/coq/gallina",
      "peacoq-ts/coq/message",
      "peacoq-ts/coq/ppcmd-token",
      "peacoq-ts/coq/status",
      "peacoq-ts/coq/xml-tag",
      "peacoq-ts/coq/cases-pattern-expr",
      "peacoq-ts/coq/explicitation",
      "peacoq-ts/coq/glob-sort-gen",
      "peacoq-ts/coq/name-base",
      "peacoq-ts/coq/ppcut",
      "peacoq-ts/coq/str-token",
      "peacoq-ts/coq/xml-tree",
      "peacoq-ts/coq-string-utils",
      "peacoq-ts/setup",
      "peacoq-ts/utils",
    ], function() {
    });
  });
