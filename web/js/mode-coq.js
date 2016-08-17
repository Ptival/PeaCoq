define(function(require, exports, module) {
  "use strict";

  var oop = require("ace/lib/oop");
  var TextMode = require("ace/mode/text").Mode;
  var CoqHighlightRules = require("./highlight-coq").CoqHighlightRules;
  var MatchingBraceOutdent = require("ace/mode/matching_brace_outdent").MatchingBraceOutdent;
  var Range = require("ace/range").Range;

  var Mode = function() {
    this.HighlightRules = CoqHighlightRules;
    this.$outdent = new MatchingBraceOutdent();
  };
  oop.inherits(Mode, TextMode);

  var indenter = /(?:=>)\s*$/;

  (function() {

    this.toggleCommentLines = function(state, doc, startRow, endRow) {
      var i, line;
      var outdent = true;
      var re = /^\s*\(\*(.*)\*\)/;

      for (i = startRow; i <= endRow; i++) {
        if (!re.test(doc.getLine(i))) {
          outdent = false;
          break;
        }
      }

      var range = new Range(0, 0, 0, 0);
      for (i = startRow; i <= endRow; i++) {
        line = doc.getLine(i);
        range.start.row = i;
        range.end.row = i;
        range.end.column = line.length;

        doc.replace(range, outdent ? line.match(re)[1] : "(*" + line +
          "*)");
      }
    };

    this.getNextLineIndent = function(state, line, tab) {
      var indent = this.$getIndent(line);
      var tokens = this.getTokenizer().getLineTokens(line, state).tokens;

      if (!(tokens.length && tokens[tokens.length - 1].type ===
          'comment') &&
        state === 'start' && indenter.test(line))
        indent += tab;
      return indent;
    };

    this.checkOutdent = function(state, line, input) {
      return this.$outdent.checkOutdent(line, input);
    };

    this.autoOutdent = function(state, doc, row) {
      this.$outdent.autoOutdent(doc, row);
    };

    this.$id = "ace/mode/coq";
  }).call(Mode.prototype);

  exports.Mode = Mode;
});
