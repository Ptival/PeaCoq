requirejs.config({
  baseUrl: 'js/lib',
  paths: {
    ace: './ace',
    "peacoq-ts": '../peacoq-ts',
  },
  shim: {
    'peacoq-ts/mathjax': {
      deps: ['MathJax-master/MathJax']
    },
    'MathJax-master/MathJax': {
      deps: ['jquery']
    },
  }
});

// Start the main app logic.
requirejs(['jquery', 'lodash', 'MathJax-master/MathJax', 'peacoq-ts/mathjax']);
