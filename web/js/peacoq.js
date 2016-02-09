requirejs.config({
  baseUrl: 'js/lib',
  paths: {
    ace: './ace',
    "peacoq-js": '../peacoq-js',
    "peacoq-ts": '../peacoq-ts',
  },
  shim: {
    'bootstrap': {
      deps: ['jquery']
    },
    'jquery.hotkeys': {
      deps: ['jquery']
    },
    'MathJax-master/MathJax': {
      deps: ['jquery']
    }
  }
});

// Start the main app logic.
requirejs([
    'ace/ace',
    'd3',
    'jquery',
    'jquery.hotkeys',
    'bootstrap',
    'lodash',
    'MathJax-master/MathJax',
  ],
  function(ace, $, bootstrap, lodash) {
    window.ace = ace;
    requirejs([
      'ace/mode/ocaml',
      'peacoq-js/highlight-coq',
      'peacoq-js/mode-coq',
      'peacoq-ts/coqtop85',
    ], function() {
      requirejs(['peacoq-ts/coq85']);
      requirejs(['peacoq-ts/utils']);
      requirejs(['peacoq-ts/coq-constr-expr']);
      requirejs(['peacoq-ts/coq-definitions']);
      requirejs(['peacoq-ts/coq-pretty-printer']);
      requirejs(['peacoq-ts/visualizations']);
      requirejs(['peacoq-ts/gallina']);
      requirejs(['peacoq-ts/goal']);
      requirejs(['peacoq-ts/prooftreenode']);
      requirejs(['peacoq-ts/fakenode']);
      requirejs(['peacoq-ts/goalnode']);
      requirejs(['peacoq-ts/tacticgroupnode']);
      requirejs(['peacoq-ts/tacticnode']);
      requirejs(['peacoq-ts/prooftree']);
    });
  });
