const nodePath = "../node_modules";

requirejs.config({
  paths: {
    "ace":            `${nodePath}/ace-code-editor/lib/ace`,
    "bootstrap":      `${nodePath}/bootstrap/dist/js/bootstrap`,
    "d3":             `${nodePath}/d3/d3`,
    "jquery":         `${nodePath}/jquery/dist/jquery`,
    "jquery.hotkeys": `${nodePath}/jquery.hotkeys/jquery.hotkeys`,
    "jquery-ui":      `${nodePath}/jquery-ui/jquery-ui`,
    "jss":            `${nodePath}/jss-browserify/jss`,
    "lodash":         `${nodePath}/lodash/lodash`,
    "MathJax":        `${nodePath}/mathjax/MathJax`,
    "polymer-ts":     `${nodePath}/polymer-ts/polymer-ts.min`,
    "rect":           `${nodePath}/packery/js/rect`,
    "rx":             `${nodePath}/rx/dist/rx.all`,
    "tsmonad":        `${nodePath}/tsmonad/dist/tsmonad`,
    "w2ui":           `${nodePath}/w2ui/w2ui`,
    "webcomponents":  `${nodePath}/npm-polymer-elements/webcomponentsjs/webcomponents-lite.min`,
  },
  shim: {
    "bootstrap": { deps: ["jquery"] },
    "jquery-ui": { deps: ["jquery"] },
    "jquery.hotkeys": { deps: ["jquery"] },
    "packery": { deps: ["jquery"] },
    "w2ui": { deps: ["jquery"] },
  },
  waitSeconds: 0,
});

// Start the main app logic.

// first, the ones that need binding
requirejs(
  [
    "ace/ace",
    "jquery",
  ],
  (ace) => {
    window.ace = ace;
    // not sure how else this is usually done
    aceRequires = [
      ace.require("ace/anchor"),
      ace.require("ace/range"),
    ];
    window.AceAjax = $.extend({}, ...aceRequires);
    requirejs(
      [
        "bootstrap",
        "d3",
        "jquery.hotkeys",
        "jquery-ui",
        "jss",
        "lodash",
        "MathJax",
        "polymer-ts",
        "rx",
        "tsmonad",
        "webcomponents",
        "w2ui",
      ],
      () => require(
        [
          "ace/mode/ocaml",
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
          // "peacoq-js-of-ts/ui-container",
          // "peacoq-js-of-ts/ui-widget",
        ]
      )
    );
  }
);
