/* @flow */

'use strict';

var Editor = require('./editor');
var GoalNode = require('./goalnode');
var ProofTree = require('./prooftree');
var ProofTreeNode = require('./prooftreenode');

var activeProofTree: ? ProofTree.ProofTree = undefined;
var activeProofTrees: Array < ProofTree > = [];
var autoLayout: bool = true;
var namesPossiblyInScope: Array < string > = [];
var svgPanEnabled: bool = false;

var cm: CodeMirrorInstance = CodeMirror(
  $("#main-left")[0], {
    "autofocus": true,
    "cursorScrollMargin": 40,
    "extraKeys": {

      "Ctrl-Alt-Up": function(cm) {
        //onCtrlUp(true);
      },

      "Ctrl-Alt-Right": function(cm) {},

      "Ctrl-Alt-Down": function(cm) {
        //onCtrlDown(true);
      },

      "Ctrl-Alt-Left": function(cm) {},

      "Ctrl-Alt-L": function(cm) {
        $("#load-local-button").click();
      },

      "Ctrl-Alt-N": function(cm) {
        //onCtrlDown(true);
      },

      "Ctrl-Alt-P": function(cm) {
        //onCtrlUp(true);
      },

      "Ctrl-Alt-S": function(cm) {
        $("#save-local-button").click();
      },

      "Ctrl-Alt-T": function(cm) {
        if ($("#peek-button").css("display") !== "none") {
          $("#peek-button").click();
          return;
        }
        if ($("#unpeek-button").css("display") !== "none") {
          $("#unpeek-button").click();
          return;
        }
      },

      "Ctrl-Alt-Enter": function(cm) {
        //onCtrlEnter();
      },

    },
    "keyMap": "sublime",
    "lineNumbers": true,
    "lineWrapping": true,
    "matchBrackets": true,
    "mode": "text/x-coq",
    "placeholder": "(* Type your Coq code here or load a file *)",
    "showCursorWhenSelecting": true,
    "styleSelectedText": true,
  }
);

var doc: Doc = cm.getDoc();

var cmContext: CodeMirrorInstance = CodeMirror(
  $("#coqtop-context")[0], {
    "lineWrapping": true,
    "matchBrackets": true,
    "mode": "text/x-coq",
  }
);

var docContext: Doc = cmContext.getDoc();

var cmResponse: CodeMirrorInstance = CodeMirror(
  $("#coqtop-response")[0], {
    "lineWrapping": true,
    "matchBrackets": true,
    "mode": "text/x-coq",
  }
);

var docResponse: Doc = cmResponse.getDoc();

var zeroPos = {
  "line": 0,
  "ch": 0
};
var mProved = Editor.markRegionDoc(doc, zeroPos, zeroPos, "proved", true);
var mProving = Editor.markRegionDoc(doc, zeroPos, zeroPos, "proving", true);
var mToprove = Editor.markRegionDoc(doc, zeroPos, zeroPos, "toprove", true);
var mUnlocked = Editor.markRegionDoc(doc, zeroPos, zeroPos, "unlocked",
  true);

function makeGroup(name: string, tactics: Array < string > ): Group {
  return {
    "name": name,
    "tactics": _(tactics).map(function(s) {
      return s + '.';
    }).value(),
  };
}

function lectureTactics(pt: ProofTree): Array < Group > {

  var curGoal: GoalNode = pt.getCurrentGoal();

  console.log(curGoal.hyps);

  var curHyps = _(curGoal.hyps).map(function(h) {
    return h.hName;
  }).reverse();
  var curNames = _(curHyps).union(namesPossiblyInScope.reverse());

  var res = [

    makeGroup(
      "terminators", ["reflexivity", "discriminate", "assumption",
        "eassumption",
      ]
    ),

    makeGroup(
      "autos", ["auto", "eauto"]
    ),

    makeGroup(
      "introductions", ["intros", "intro"]
    ),

    makeGroup(
      "break_if, f_equal, subst", ["break_if", "f_equal", "repeat f_equal",
        "subst"
      ]
    ),

    makeGroup(
      "simplifications", ["simpl"].concat(
        _(curHyps).map(function(h) {
          return "simpl in " + h;
        }).value()
      ).concat(["simpl in *"])
    ),

    makeGroup(
      "constructors", ["left", "right", "split", "constructor",
        "econstructor",
        "eexists"
      ]
    ),

    makeGroup(
      "destructors",
      _(curHyps).map(function(h) {
        return "destruct " + h;
      }).value()
    ),

    makeGroup(
      "inductions",
      _(curHyps).map(function(h) {
        return "induction " + h;
      }).value()
    ),

    makeGroup(
      "inversions",
      _(curHyps).map(function(h) {
        return "inversion " + h;
      }).value()
    ),

    makeGroup(
      "solvers", ["congruence", "omega", "firstorder"]
    ),

    makeGroup(
      "applications",
      _(curNames).map(function(n) {
        return "apply " + n;
      }).value()
      .concat(
        _(curNames).map(function(n) {
          return "eapply " + n;
        }).value()
      )
    ),

    makeGroup(
      "rewrites",
      _(curNames).map(function(n) {
        return "rewrite -> " + n;
      }).value()
      .concat(
        _(curNames).map(function(n) {
          return "rewrite <- " + n;
        }).value()
      )
    ),

    makeGroup(
      "applications in",
      _(curNames).map(function(n) {
        return _(curHyps)
          .map(function(h) {
            if (h === n) {
              return [];
            }
            return ([
              "apply " + n + " in " + h,
              "eapply " + n + " in " + h
            ]);
          })
          .flatten(true).value();
      }).flatten(true).value()
    ),

    makeGroup(
      "rewrites in",
      _(curNames).map(function(n) {
        return _(curHyps)
          .map(function(h) {
            if (h === n) {
              return [];
            }
            return ([
              ("rewrite -> " + n + " in " + h), ("rewrite <- " + n +
                " in " + h)
            ]);
          })
          .flatten(true).value();
      }).flatten(true).value()
    ),

    makeGroup(
      "reverts",
      _(curHyps).map(function(h) {
        return "revert " + h;
      }).value()
    ),

  ];

  return res;

}

module.exports = {
  "activeProofTree": activeProofTree,
  "autoLayout": autoLayout,
  "cm": cm,
  "cmContext": cmContext,
  "cmResponse": cmResponse,
  "doc": doc,
  "docContext": docContext,
  "docResponse": docResponse,
  "lectureTactics": lectureTactics,
  "mProved": mProved,
  "mProving": mProving,
  "mToprove": mToprove,
  "mUnlocked": mUnlocked,
  "namesPossiblyInScope": namesPossiblyInScope,
  "svgPanEnabled": svgPanEnabled,
}
