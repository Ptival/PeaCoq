const nodePath = "./node_modules";

requirejs.config({
    paths: {
        "ace": `${nodePath}/ace-code-editor/lib/ace`,
        "bluebird": `${nodePath}/bluebird/js/browser/bluebird`,
        "bootstrap": `${nodePath}/bootstrap/dist/js/bootstrap.bundle`,
        "codemirror": `${nodePath}/codemirror/lib/codemirror`,
        "d3-array": `${nodePath}/d3-array/build/d3-array`,
        "d3-collection": `${nodePath}/d3-collection/build/d3-collection`,
        "d3-color": `${nodePath}/d3-color/build/d3-color`,
        "d3-dispatch": `${nodePath}/d3-dispatch/build/d3-dispatch`,
        "d3-ease": `${nodePath}/d3-ease/build/d3-ease`,
        "d3-format": `${nodePath}/d3-format/build/d3-format`,
        "d3-hierarchy": `${nodePath}/d3-hierarchy/dist/d3-hierarchy`,
        "d3-interpolate": `${nodePath}/d3-interpolate/build/d3-interpolate`,
        "d3-path": `${nodePath}/d3-path/build/d3-path`,
        "d3-time": `${nodePath}/d3-time/build/d3-time`,
        "d3-time-format": `${nodePath}/d3-time-format/build/d3-time-format`,
        "d3-timer": `${nodePath}/d3-timer/build/d3-timer`,
        "d3-transition": `${nodePath}/d3-transition/build/d3-transition`,
        "d3-scale": `${nodePath}/d3-scale/dist/d3-scale`,
        "d3-selection": `${nodePath}/d3-selection/dist/d3-selection`,
        "jquery": `${nodePath}/jquery/dist/jquery`,
        "jquery-contextmenu": `${nodePath}/jquery-contextmenu/dist/jquery.contextMenu.min`,
        "jquery.hotkeys": `${nodePath}/jquery.hotkeys/jquery.hotkeys`,
        "jquery-ui": `${nodePath}/jquery-ui/jquery-ui`,
        "jquery.ui.position": `${nodePath}/jquery-contextmenu/dist/jquery.ui.position.min`,
        "jss": `${nodePath}/jss-browserify/jss`,
        "lodash": `${nodePath}/lodash/lodash`,
        "MathJax": `${nodePath}/mathjax/MathJax`,
        // "polymer-ts": `${nodePath}/polymer-ts/polymer-ts.min`,
        // "popper.js": `${nodePath}/popper.js/dist/umd/popper`,
        // "rect": `${nodePath}/packery/js/rect`,
        // "react": `${nodePath}/react/dist/react`,
        // "react-codemirror": `${nodePath}/react-codemirror/dist/react-codemirror`,
        // "react-dom": `${nodePath}/react-dom/dist/react-dom`,
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
        // "packery": { deps: ["jquery"] },
        // "react-codemirror": { deps: ["react", "react-dom"] },
        "w2ui": { deps: ["jquery"] },
    },
    waitSeconds: 0,
});

// Start the main app logic.
const startRequire = Date.now()

// first, the ones that need binding
requirejs(
    [
        "ace/ace", // ~ 500ms
        // "bluebird", // ~ 100ms
        "codemirror", // ~100ms
        "jquery", // ~ 100ms
        // "popper.js",
        "s-expression", // ~ 30ms
    ],
    (
        ace,
        // bluebird,
        _codeMirror,
        _jquery,
        // popper,
        sexpParse
    ) => {
        // window.Popper = popper
        const pass1 = Date.now()
        console.log(`Required 1st pass: ${pass1 - startRequire}ms`)
        window.ace = ace;
        // window.Promise = bluebird;
        // not sure how else this is usually done
        aceRequires = [
          ace.require("ace/anchor"),
          ace.require("ace/range"),
        ];
        window.AceAjax = $.extend({}, ...aceRequires);
        window.sexpParse = sexpParse;
        requirejs(
            [
                "bootstrap", // ~50ms
                "jquery.hotkeys", // ~20ms
                "jquery-contextmenu", // ~40ms
                // "jquery-ui",
                "jss", // ~ 20ms
                "lodash", // ~60ms
                "MathJax", // ~40ms
                // "polymer-ts",
                "rx", // ~60ms
                "tsmonad", // ~100ms
                // "webcomponents",
                "w2ui", // ~80ms
            ],
            (_1, _2, _3, _4, _5, _6, _7, TsMonad, _8, _9) => {
                window.TsMonad = TsMonad
                const pass2 = Date.now()
                console.log(`Required 2nd pass: ${pass2 - pass1}ms`)
                require(
                    [
                        "ace/ext/language_tools",
                        "ace/mode/ocaml",
                        "d3-hierarchy",
                        "d3-scale",
                        "d3-selection",
                        "js/highlight-coq",
                        "js/mode-coq",
                        // Unfortunately, at the moment, all these have been written as non-modules
                        "js-of-ts/coq/binder-kind",
                        "js-of-ts/coq/case-style",
                        "js-of-ts/coq/feedback-content",
                        "js-of-ts/coq/paren-relation",
                        "js-of-ts/coq/prim-token",
                        "js-of-ts/coq/binding-kind",
                        "js-of-ts/coq/feedback",
                        "js-of-ts/coq/message-level",
                        "js-of-ts/coq/ppbox",
                        "js-of-ts/coq/reference",
                        "js-of-ts/coq/value-fail",
                        // "js-of-ts/coq/block-type",
                        "js-of-ts/coq/gallina",
                        // "js-of-ts/coq/message",
                        "js-of-ts/coq/status",
                        "js-of-ts/coq/xml-tag",
                        "js-of-ts/coq/explicitation",
                        "js-of-ts/coq/glob-sort-gen",
                        "js-of-ts/coq/name-base",
                        "js-of-ts/coq/ppcut",
                        // "js-of-ts/coq/str-token",
                        "js-of-ts/coq/xml-tree",
                        "js-of-ts/peacoq/coq-string-utils",
                        "js-of-ts/peacoq/utils",
                        "js-of-ts/index",
                        // "js-of-ts/ui-container",
                        // "js-of-ts/ui-widget",
                    ],
                    () => {
                        const pass3 = Date.now()
                        console.log(`Required 3rd pass: ${pass3 - pass2}ms`)
                    })
            }
        );
    }
);
