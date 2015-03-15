(function(mod) {
    if (typeof exports == "object" && typeof module == "object") // CommonJS
        mod(require("../../lib/codemirror"));
    else if (typeof define == "function" && define.amd) // AMD
        define(["../../lib/codemirror"], mod);
    else // Plain browser env
        mod(CodeMirror);
})(function(CodeMirror) {
    "use strict";

    CodeMirror.defineMode('coq', function(_config, parserConfig) {

        var vernacular = [
            'Add', 'All', 'Arguments', 'Axiom',
            'Bind',
            'Canonical', 'Check', 'Class', 'Close', 'Coercion', 'CoFixpoint',
            'CoInductive', 'Context', 'Contextual', 'Corollary',
            'Defined', 'Definition', 'Delimit',
            'Eval',
            'End', 'Example', 'Export',
            'Fact', 'Fixpoint',
            'Global', 'Goal', 'Graph',
            'Hint', 'Hypotheses', 'Hypothesis',
            'Implicit', 'Implicits', 'Import', 'Inductive', 'Infix', 'Instance',
            'Lemma', 'Let', 'Local', 'Ltac',
            'Module', 'Morphism',
            'Notation',
            'Open',
            'Parameter', 'Parameters', 'Prenex', 'Print', 'Printing', 'Program',
            'Projections', 'Proof',
            'Proposition',
            'Qed',
            'Record', 'Relation', 'Remark', 'Require', 'Reserved', 'Resolve', 'Rewrite',
            'Save', 'Scope', 'Search', 'Section', 'Set', 'Show', 'Strict', 'Structure',
            'Tactic', 'Theorem',
            'Unset',
            'Variable', 'Variables', 'View',
        ];

        var gallina = [
            'as',
            'cofix',
            'else', 'end', 'exists',
            'fix', 'for', 'forall',
            'if', 'in', 'is',
            'let',
            'match',
            'of',
            'Prop',
            'return',
            'Set', 'struct',
            'then', 'Type',
            'when', 'with',
        ];

        var tactics = [
            'apply',
            'case', 'clear',
            'dependent',
            'elim',
            'firstorder',
            'generalize',
            'hnf',
            'induction', 'intro', 'intros',
            'move',
            'pattern', 'pose',
            'rename',
            'set', 'simpl',
        ];

        var terminators = [
            'assumption',
            'contradiction',
            'discriminate',
            'exact',
            'omega',
            'reflexivity',
            'tauto',
        ];

        var words = {};

        _(vernacular).each(function(word) {
            words[word] = 'builtin';
        });

        _(gallina).each(function(word) {
            words[word] = 'keyword';
        });

        _(tactics).each(function(word) {
            words[word] = 'tactic';
        });

        _(terminators).each(function(word) {
            words[word] = 'terminator';
        });

//            'let': 'keyword',
//            'print_endline': 'builtin',
//            'true': 'atom',

        function tokenBase(stream, state) {
            var ch = stream.next();

            if (ch === '"') {
                state.tokenize = tokenString;
                return state.tokenize(stream, state);
            }

            if (ch === '(') {
                if (stream.eat('*')) {
                    state.commentLevel++;
                    state.tokenize = tokenComment;
                    return state.tokenize(stream, state);
                }
            }

            if (ch === '~') {
                stream.eatWhile(/\w/);
                return 'variable-2';
            }

            if (ch === '`') {
                stream.eatWhile(/\w/);
                return 'quote';
            }

            if (/\d/.test(ch)) {
                stream.eatWhile(/[\d]/);
                if (stream.eat('.')) {
                    stream.eatWhile(/[\d]/);
                }
                return 'number';
            }

            if ( /[+\-*&%=<>!?|]/.test(ch)) {
                return 'operator';
            }

            stream.eatWhile(/\w/);
            var cur = stream.current();
            return words.hasOwnProperty(cur) ? words[cur] : 'variable';
        }

        function tokenString(stream, state) {
            var next, end = false, escaped = false;
            while ((next = stream.next()) != null) {
                if (next === '"' && !escaped) {
                    end = true;
                    break;
                }
                escaped = !escaped && next === '\\';
            }
            if (end && !escaped) {
                state.tokenize = tokenBase;
            }
            return 'string';
        };

        function tokenComment(stream, state) {
            var prev, next;
            while(state.commentLevel > 0 && (next = stream.next()) != null) {
                if (prev === '(' && next === '*') state.commentLevel++;
                if (prev === '*' && next === ')') state.commentLevel--;
                prev = next;
            }
            if (state.commentLevel <= 0) {
                state.tokenize = tokenBase;
            }
            return 'comment';
        }

        return {
            startState: function() {
                return {tokenize: tokenBase, commentLevel: 0};
            },
            token: function(stream, state) {
                if (stream.eatSpace()) return null;
                return state.tokenize(stream, state);
            },
            blockCommentStart: "(*",
            blockCommentEnd: "*)",
            lineComment: null
        };
    });

    CodeMirror.defineMIME('text/x-coq', {
        name: 'coq',
    });

});
