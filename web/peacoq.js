const nodePath = "./node_modules";

requirejs.config({
  paths: {
    "ace": `${nodePath}/ace-code-editor/lib/ace`,
    "bluebird": `${nodePath}/bluebird/js/browser/bluebird`,
    "bootstrap": `${nodePath}/bootstrap/dist/js/bootstrap`,
    "d3-array": `${nodePath}/d3-array/build/d3-array`,
    "d3-collection": `${nodePath}/d3-collection/build/d3-collection`,
    "d3-color": `${nodePath}/d3-color/build/d3-color`,
    "d3-format": `${nodePath}/d3-format/build/d3-format`,
    "d3-hierarchy": `${nodePath}/d3-hierarchy/build/d3-hierarchy`,
    "d3-interpolate": `${nodePath}/d3-interpolate/build/d3-interpolate`,
    "d3-path": `${nodePath}/d3-path/build/d3-path`,
    "d3-time": `${nodePath}/d3-time/build/d3-time`,
    "d3-time-format": `${nodePath}/d3-time-format/build/d3-time-format`,
    "d3-scale": `${nodePath}/d3-scale/build/d3-scale`,
    "d3-selection": `${nodePath}/d3-selection/build/d3-selection`,
    "jquery": `${nodePath}/jquery/dist/jquery`,
    "jquery-contextmenu": `${nodePath}/jquery-contextmenu/dist/jquery.contextMenu.min`,
    "jquery.hotkeys": `${nodePath}/jquery.hotkeys/jquery.hotkeys`,
    "jquery-ui": `${nodePath}/jquery-ui/jquery-ui`,
    "jquery.ui.position": `${nodePath}/jquery-contextmenu/dist/jquery.ui.position.min`,
    "jss": `${nodePath}/jss-browserify/jss`,
    "lodash": `${nodePath}/lodash/lodash`,
    "MathJax": `${nodePath}/mathjax/MathJax`,
    // "polymer-ts": `${nodePath}/polymer-ts/polymer-ts.min`,
    // "rect": `${nodePath}/packery/js/rect`,
    "rx": `${nodePath}/rx/dist/rx.all`,
    "s-expression": `${nodePath}/s-expression-amd/index`,
    "tsmonad": `${nodePath}/tsmonad/dist/tsmonad`,
    "w2ui": `${nodePath}/w2ui/w2ui`,
    // "webcomponents": `${nodePath}/npm-polymer-elements/webcomponentsjs/webcomponents-lite.min`,
  },
  shim: {
    "bootstrap": { deps: ["jquery"] },
    "jquery-contextmenu": { deps: ["jquery", "jquery.ui.position"] },
    "jquery.hotkeys": { deps: ["jquery"] },
    "jquery-ui": { deps: ["jquery"] },
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
    "bluebird",
    "s-expression",
    "jquery",
  ],
  (ace, bluebird, sexpParse) => {
    window.ace = ace;
    window.Promise = bluebird;
    // not sure how else this is usually done
    aceRequires = [
      ace.require("ace/anchor"),
      ace.require("ace/range"),
    ];
    window.AceAjax = $.extend({}, ...aceRequires);
    window.sexpParse = sexpParse;
    requirejs(
      [
        "bootstrap",
        "jquery.hotkeys",
        "jquery-contextmenu",
        // "jquery-ui",
        "jss",
        "lodash",
        "MathJax",
        // "polymer-ts",
        "rx",
        "tsmonad",
        // "webcomponents",
        "w2ui",
      ],
      () => require(
        [
          "ace/ext/language_tools",
          "ace/mode/ocaml",
          "js/highlight-coq",
          "js/mode-coq",
          // Unfortunately, at the moment, all these have been written as non-modules
          "js-of-ts/coq/binder-kind",
          "js-of-ts/coq/case-style",
          "js-of-ts/coq/feedback-content",
          "js-of-ts/coq/local-binder",
          "js-of-ts/coq/paren-relation",
          "js-of-ts/coq/prim-token",
          "js-of-ts/coq/unparsing",
          "js-of-ts/coq/binding-kind",
          "js-of-ts/coq/coq-constr-expr",
          "js-of-ts/coq/feedback",
          "js-of-ts/coq/message-level",
          "js-of-ts/coq/ppbox",
          "js-of-ts/coq/reference",
          "js-of-ts/coq/value-fail",
          "js-of-ts/coq/block-type",
          "js-of-ts/coq/gallina",
          // "js-of-ts/coq/message",
          "js-of-ts/coq/ppcmd-token",
          "js-of-ts/coq/status",
          "js-of-ts/coq/xml-tag",
          "js-of-ts/coq/cases-pattern-expr",
          "js-of-ts/coq/explicitation",
          "js-of-ts/coq/glob-sort-gen",
          "js-of-ts/coq/name-base",
          "js-of-ts/coq/ppcut",
          "js-of-ts/coq/str-token",
          "js-of-ts/coq/xml-tree",
          "js-of-ts/peacoq/coq-string-utils",
          "js-of-ts/peacoq/utils",
          "js-of-ts/index",
          // "js-of-ts/ui-container",
          // "js-of-ts/ui-widget",
        ]
      )
    );
  }
);
