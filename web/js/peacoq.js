requirejs.config({
  baseUrl: 'js/lib',
  paths: {
    ace: './ace',
    "peacoq-js": '../peacoq-js',
    "peacoq-ts": '../peacoq-ts',
  },
  shim: {
    'bootstrap': { deps: ['jquery'] },
    'jquery.hotkeys': { deps: ['jquery'] },
    'MathJax-master/MathJax': { deps: ['jquery'] },
    'peacoq-ts/coq85': { deps: ['peacoq-ts/coqtop85', 'peacoq-ts/utils'] },
    'peacoq-ts/coq-pretty-printer': { deps: ['peacoq-ts/coq-definitions'] },
    'peacoq-ts/editor-tab': { deps: ['peacoq-ts/tab'] },
    'peacoq-ts/fakenode': { deps: ['peacoq-ts/prooftreenode'] },
    'peacoq-ts/goalnode': { deps: ['peacoq-ts/prooftreenode'] },
    'peacoq-ts/tacticgroupnode': { deps: ['peacoq-ts/prooftreenode'] },
    'peacoq-ts/setup': { deps: [
      'peacoq-ts/coq85',
      'peacoq-ts/coqtop85',
      'peacoq-ts/coqtop-rx',
      'peacoq-ts/editor-tab',
      'peacoq-ts/prooftree',
      'peacoq-ts/theme',
      'peacoq-ts/toolbar'
    ] },
    'peacoq-ts/utils': { deps: ['tsmonad'] },
    'peacoq-ts/prooftree': { deps: ['peacoq-ts/prooftree-utils']},
    'w2ui/w2ui': { deps: ['jquery'] },
  }
});

// Start the main app logic.
requirejs([
    'ace/ace',
    'd3',
    'jquery',
    //'jquery-ui/jquery-ui',
    'jquery.hotkeys',
    'bootstrap',
    'jss',
    'lodash',
    'MathJax-master/MathJax',
    'rx.all',
    'tsmonad',
    'w2ui/w2ui',
  ],
  function(ace, d3, $) {
    window.ace = ace;
    requirejs([
      'ace/mode/ocaml',
      'peacoq-js/highlight-coq',
      'peacoq-js/mode-coq',
      'peacoq-ts/coq-string-utils',
      'peacoq-ts/coqtop-rx',
      'peacoq-ts/coqtop85',
      'peacoq-ts/coq85',
      'peacoq-ts/keybindings',
      'peacoq-ts/setup',
      'peacoq-ts/editor-tab',
      'peacoq-ts/tab',
      'peacoq-ts/theme',
      'peacoq-ts/toolbar',
      'peacoq-ts/prooftree',
      'peacoq-ts/ui-rx',
    ], function() {
      requirejs(['peacoq-ts/coq-constr-expr']);
      requirejs(['peacoq-ts/coq-definitions']);
      requirejs(['peacoq-ts/coq-pretty-printer']);
      //requirejs(['peacoq-ts/coq85']);
      requirejs(['peacoq-ts/edits']);
      requirejs(['peacoq-ts/fakenode']);
      requirejs(['peacoq-ts/gallina']);
      requirejs(['peacoq-ts/goal']);
      requirejs(['peacoq-ts/goalnode']);
      //requirejs(['peacoq-ts/prooftree']);
      requirejs(['peacoq-ts/prooftree-utils']);
      requirejs(['peacoq-ts/prooftreenode']);
      //requirejs(['peacoq-ts/setup']);
      requirejs(['peacoq-ts/show']);
      requirejs(['peacoq-ts/tacticgroupnode']);
      requirejs(['peacoq-ts/tactic']);
      //requirejs(['peacoq-ts/theme']);
      requirejs(['peacoq-ts/utils']);
      requirejs(['peacoq-ts/visualizations']);
    });
  });
