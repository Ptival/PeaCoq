/* @flow */

'use strict';

var Editor = require('./editor');
var Globals = require('./globals');
var ProofTree = require('./prooftree');
var PeaCoqResponse = require('./peacoqresponse');
var Utils = require('./utils');

var processing: bool = false;
var nbsp: string = "\u00A0";
var focusedOnEditor: bool = true;

$(document).ready(function() {

  $(window).bind('beforeunload', function() {
    return 'WARNING: unsaved progress wil be lost';
  });

  var buttonGroup = $(".btn-group");

  $("<button>", {
      "class": "btn btn-default",
      "id": "prover-down",
    })
    .appendTo(buttonGroup)
    .on("click", function() {
      Editor.onCtrlDown(true);
    })
    .append(mkGlyph("arrow-down"));

  $("<button>", {
      "class": "btn btn-default",
      "id": "prover-up",
    })
    .appendTo(buttonGroup)
    .on("click", function() {
      Editor.onCtrlUp(true);
    })
    .append(mkGlyph("arrow-up"))
    .append(nbsp + "Prev");

  $("<button>", {
      "class": "btn btn-default",
      "id": "prover-caret",
    })
    .appendTo(buttonGroup)
    .on("click", function() {
      Editor.onCtrlEnter();
    })
    .append(mkGlyph("arrow-right"))
    .append(mkGlyph("italic"))
    .append(nbsp + "Go to caret");

  $("<button>", {
      "class": "btn btn-default",
      "html": $("<span>")
        .append(mkGlyph("edit"))
        .append(nbsp + "View Editor"),
      "id": "peek-button",
    })
    .appendTo(buttonGroup)
    .css("display", "none")
    .on("click", focusEditorUI);

  $("<button>", {
      "class": "btn btn-default",
      "html": $("<span>")
        .append(mkGlyph("tree-deciduous"))
        .append(nbsp + "View Proof Tree"),
      "id": "unpeek-button",
    })
    .appendTo(buttonGroup)
    .css("display", "none")
    .on("click", focusProofTreeUI);

});

function mkGlyph(name: string): Element {
  return $("<i>", {
    "class": "glyphicon glyphicon-" + name,
  });
}

function onRequestTriggered(requestType: string, request: string) {
  switch (requestType) {
    case 'query':
      break;
  }
}

function resize() {
  var windowHeight = $(window).height();
  var width = $(window).width();
  var height = $("#prooftree").height();
  var proofTree = Globals.activeProofTree;
  if (proofTree) {
    proofTree.resize($(window).width(), height);
  }
  resizeCoqtopPanes();
  Editor.scrollIntoView();
}

function resizeCoqtopPanes() {

  if (focusedOnEditor) {

    var contextLength = Globals.docContext.getValue().length;
    var responseLength = Globals.docResponse.getValue().length;

    if (contextLength === 0 && responseLength === 0) {
      $("#coqtop-context").height("50%");
      $("#coqtop-response").height("50%");
    } else if (contextLength === 0) {
      $("#coqtop-context").height("0%");
      $("#coqtop-response").height("100%");
    } else if (responseLength === 0) {
      $("#coqtop-context").height("100%");
      $("#coqtop-response").height("0%");
    } else {
      $("#coqtop-context").height("80%");
      $("#coqtop-response").height("20%");
    }

  } else {

    $("#coqtop-context").height("0%");
    $("#coqtop-response").height("100%");

  }

}

function focusEditorUI() {

  focusedOnEditor = true;

  $("#main").height("100%");
  $("#prooftree").height("0%");

  $("#peek-button").css("display", "none");
  $("#unpeek-button").css("display", "");

  resize();
  Globals.cm.refresh();
  Editor.scrollIntoView();
  Globals.cm.focus();

}

function focusProofTreeUI() {

  focusedOnEditor = false;

  $("#main").height("30%");
  $("#prooftree").height("70%");

  $("#peek-button").css("display", "");
  $("#unpeek-button").css("display", "none");

  $("#coqtop-context").height("0%");
  $("#coqtop-response").height("100%");

  resize();
  Globals.cm.refresh();
  Editor.scrollIntoView();
  var activeProofTree = Globals.activeProofTree;
  if (activeProofTree) {
    activeProofTree.getFocus();
    activeProofTree.refreshTactics();
  }

}

module.exports = {
  "focusEditorUI": focusEditorUI,
  "focusProofTreeUI": focusProofTreeUI,
  "onRequestTriggered": onRequestTriggered,
};
