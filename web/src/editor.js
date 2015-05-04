/* @flow */

'use strict';

var Coqtop = require('./coqtop');
var Globals = require('./globals');
var Goal = require('./goal');
var Lecture = require('./lecture');
var PeaCoqResponse = require('./peacoqresponse');
var ProofTree = require('./prooftree');
var Utils = require('./utils');

var cmContext, docContext, cmResponse, docResponse;

var setCursorOnResponse: bool = false;

function onCtrlDown(fromUser: bool): Promise {
	var rToprove = Globals.mToprove.find();
	var rUnlocked = Globals.mUnlocked.find();
	var unlocked = Globals.doc.getRange(rUnlocked.from, rUnlocked.to);
	var nextIndex = Utils.next(unlocked);
	if (nextIndex === 0) {
		return Promise.resolve();
	}
	var nextPos = Globals.cm.findPosH(rUnlocked.from, nextIndex, "char");
	markToprove(rToprove.from, nextPos);
	markUnlocked(nextPos, rUnlocked.to);
	if (fromUser) {
		setCursorOnResponse = true;
		Globals.doc.setCursor(nextPos);
		Utils.scrollIntoView();
	}
	return processToprove();
}

function updateCoqtopPane(direction: bool, response: PeaCoqResponse): void {

	var toprove = getToprove();
	if (toprove.length !== 0) {
		Globals.docContext.setValue("");
		Globals.docResponse.setValue("");
		return;
	}

	var contents = response.contents[0];

	switch (typeof contents) {

		case "string":
			break;

		case "object":
			if (contents.length > 1) {
				alert("Found contents with length greater than 1, see log");
				console.log(contents);
			}
			contents = contents[0];
			break;

		default:
			alert(
				"Found contents with type different than string and object, see log"
			);
			console.log(typeof contents, contents);

	};

	contents = contents.trim();

	var contextContents = "";

	switch (response.tag) {

		case "Good":

			var nbFocused = response.focused.length;
			var unfocused = response.unfocused[0];

			if (nbFocused > 0) {

				_(response.focused[0].gHyps).each(function(h) {
					contextContents += ProofTree.showHypothesisText(
							Goal.extractHypothesis(h)) +
						"\n";
				});

				var goalLinePosition = contextContents.split('\n').length;

				contextContents += ProofTree.showTermText(ProofTree.extractGoal(
					response.focused[0].gGoal
				));
				contextContents += "\n\n";

				var nbUnfocused = (unfocused === undefined) ? 0 : unfocused[0].length +
					unfocused[1].length;

				if (nbUnfocused === 0) {
					contextContents += nbFocused + " subgoal" + (nbFocused <= 1 ? "" :
						"s");
				} else {
					contextContents += (
						nbFocused + " focused subgoal" + (nbFocused <= 1 ? "" : "s") +
						", " + nbUnfocused + " unfocused"
					);
				}

				_(response.focused)
					.rest()
					.each(function(g, ndx) {
						contextContents += "\n\n";
						contextContents += "subgoal " + (ndx + 2) + "\n";
						contextContents += ProofTree.showTermText(ProofTree.extractGoal(
							g.gGoal));
					});

				Globals.docContext.setValue(contextContents);

				Globals.cmContext.addLineWidget(
					goalLinePosition - 1,
					//$("<hr>").css("border", "1px solid black")[0],
					$("<div>")
					.text("__________________________________________________")[0], {
						"above": true
					}
				);

			} else if (unfocused !== undefined) {

				var nbRemaining = unfocused[0].length + unfocused[1].length;

				contextContents += (
					nbRemaining + " remaining subgoal" + (nbRemaining <= 1 ? "" : "s")
				);

				Globals.docContext.setValue(contextContents);

			} else {

				Globals.docContext.setValue(contextContents);

			}

			break;

		case "Fail":

			break;

	};

	var responseContents = Utils.stripWarning(contents);

	// postprocessing of Inductive
	if (responseContents.startsWith("Inductive")) {
		responseContents = responseContents
			.replace(/:=\s+/, ":=\n| ")
			.replace(/ \| /, "\n| ");
	}

	Globals.docResponse.setValue(responseContents);

}

var goingDown = true;
var goingUp = false;

function undoCallback(fromUser, undone, response) {
	switch (response.rResponse.tag) {
		case "Good":
			if (Globals.activeProofTree) {
				Globals.activeProofTree.onUndo(fromUser, undone, response);
			}
			var stepsToRewind = +response.rResponse.contents[0];
			//console.log("Rewinding additional " + stepsToRewind + " steps");
			while (stepsToRewind-- > 0) {
				var rProved = Globals.mProved.find();
				var rUnlocked = Globals.mUnlocked.find();
				var proved = Globals.doc.getRange(rProved.from, rProved.to);
				if (proved === "") {
					return;
				}
				var prevIndex = Utils.prev(proved);
				var pieceUnproved = proved.substring(prevIndex);
				if (pieceUnproved === "") {
					return;
				}
				var prevPos = Globals.cm.findPosH(rProved.from, prevIndex, "char");
				markProved(rProved.from, prevPos);
				markProving(prevPos, prevPos);
				markToprove(prevPos, prevPos);
				markUnlocked(prevPos, rUnlocked.to);
				if (fromUser) {
					Globals.doc.setCursor(prevPos);
					scrollIntoView();
				}
			}
			response.rResponse.contents[0] = ""; // don't show the user the steps number
			break;
	};
	updateCoqtopPane(goingUp, response);
}

function onCtrlUp(fromUser: bool): Promise {
	if (processingToprove) {
		return Promise.resolve();
	}
	var rProved = Globals.mProved.find();
	var rUnlocked = Globals.mUnlocked.find();
	var proved = Globals.doc.getRange(rProved.from, rProved.to);
	if (proved === "") {
		return Promise.resolve();
	}
	var prevIndex = Utils.prev(proved);
	var pieceToUnprocess = proved.substring(prevIndex);
	if (pieceToUnprocess === "") {
		return Promise.resolve();
	}
	var prevPos = Globals.cm.findPosH(rProved.from, prevIndex, "char");
	markProved(rProved.from, prevPos);
	markProving(prevPos, prevPos);
	markToprove(prevPos, prevPos);
	markUnlocked(prevPos, rUnlocked.to);
	Coqtop.asyncLog("PROVERUP " + pieceToUnprocess);
	if (fromUser) {
		setCursorOnResponse = true;
		Globals.doc.setCursor(prevPos);
		scrollIntoView();
	}
	return Coqtop.asyncUndo()
		.then(_.partial(undoCallback, fromUser, pieceToUnprocess));
}

function markRegionDoc(doc: Doc, from: DocumentPosition,
	to: DocumentPosition, className: string, readOnly: bool): TextMarker {
	return doc.markText(
		from,
		to, {
			"className": className,
			"clearWhenEmpty": false,
			"inclusiveLeft": true,
			"inclusiveRight": !readOnly,
			"readOnly": readOnly,
		}
	);
}

function markRegion(
	from: DocumentPosition,
	to: DocumentPosition,
	className: string,
	readOnly: bool
): TextMarker {
	return markRegion(Globals.doc, from, to, className, readOnly);
}

function markProved(from, to) {
	Globals.mProved.clear();
	Globals.mProved = markRegion(from, to, "proved", true);
}

function markProving(from, to) {
	Globals.mProving.clear();
	Globals.mProving = markRegion(from, to, "proving", true);
}

function markToprove(from, to) {
	Globals.mToprove.clear();
	Globals.mToprove = markRegion(from, to, "toprove", true);
}

function markUnlocked(from, to) {
	Globals.mUnlocked.clear();
	Globals.mUnlocked = markRegion(from, to, "unlocked", false);
}

var processingToprove = false;

function processToprove() {
	if (processingToprove) {
		return Promise.resolve();
	}
	// Here, the prooftree gets a chance to modify toprove
	/*
  if (Globals.activeProofTree !== undefined) {
		Globals.activeProofTree.beforeToproveConsumption();
	}
  */
	var rProving = Globals.mProving.find();
	var rToprove = Globals.mToprove.find();
	var toprove = Globals.doc.getRange(rToprove.from, rToprove.to);
	if (toprove === '') {
		return Promise.resolve();
	}
	var nextIndex = Utils.next(toprove);
	var pieceToProcess = toprove.substring(0, nextIndex);
	var nextPos = Globals.cm.findPosH(rToprove.from, nextIndex, "char");
	markProving(rProving.from, nextPos);
	markToprove(nextPos, rToprove.to);
	processingToprove = true;
	return Coqtop.asyncQuery(pieceToProcess)
		.then(function(response) {
			processingToprove = false;
			processToprove();
		})
		.catch(Utils.outputError);
}

function getProved() {
	var rProved = Globals.mProved.find();
	return Globals.doc.getRange(rProved.from, rProved.to);
}

function getProving() {
	var rProving = Globals.mProving.find();
	return Globals.doc.getRange(rProving.from, rProving.to);
}

function getToprove() {
	var rToprove = Globals.mToprove.find();
	return Globals.doc.getRange(rToprove.from, rToprove.to);
}

function getUnlocked() {
	var rUnlocked = Globals.mUnlocked.find();
	return Globals.doc.getRange(rUnlocked.from, rUnlocked.to);
}

function scrollIntoView() {
	var cursorPos = Globals.doc.getCursor();
	Globals.cm.scrollIntoView({
		"from": Globals.cm.findPosV(cursorPos, -1, "line"),
		"to": Globals.cm.findPosV(cursorPos, +1, "line"),
	});
}

// a <= b ?
function positionIsBefore(a, b) {
	if (a.line < b.line) {
		return true;
	}
	if (a.line === b.line && a.ch <= b.ch) {
		return true;
	}
	return false;
}

function onCtrlEnter() {
	setCursorOnResponse = false;
	var cursorPos = Globals.doc.getCursor();
	var rProved = Globals.mProved.find();
	var rUnlocked = Globals.mUnlocked.find();
	if (positionIsBefore(cursorPos, rProved.to)) {
		rewindToPos(cursorPos);
	} else if (positionIsBefore(rUnlocked.from, cursorPos)) {
		processToPos(cursorPos);
	} else { // trying to jump in the proving or toprove area, ignored
		return;
	}
}

function createProofTree(response) {

	var pt = new ProofTree(
		$("#prooftree")[0],
		$(window).width(),
		$("#prooftree").height(),
		function() {
			$("#loading").css("display", "");
		},
		function() {
			$("#loading").css("display", "none");
		}
	);

	Globals.activeProofTree = pt;

	pt.newAlreadyStartedTheorem(
		response,
		Globals.lectureTactics
	);

	// only show up the tree automatically if the user is not processing to
	// caret
	var toprove = getToprove();
	if (toprove.length === 0) {
		focusProofTreeUI();
		pt.refreshTactics();
	}

	if (Globals.autoLayout) {
		proofTreeQueryWish("Proof.");

		// TODO: insert a newline only when needed...
		//var rUnlocked = mUnlocked.find();
		//doc.replaceRange('\n  ', rUnlocked.from);

		pt.getFocus();
	}

}

function onResponse(requestType: string, request: string, response:
	PeaCoqResponse): void {

	switch (requestType) {
		case 'query':
			switch (response.tag) {

				case 'Good':
					var rProving = Globals.mProving.find();
					var proving = Globals.doc.getRange(rProving.from, rProving.to);
					if (Utils.coqTrim(proving) !== Utils.coqTrim(request)) {
						console.log(
							'request response was for', request,
							'but was expecting for', proving
						);
						return;
					}
					var rProved = Globals.mProved.find();
					var nextPos = rProving.to;
					markProved(rProved.from, nextPos);
					markProving(nextPos, rProving.to);
					/*
					if (setCursorOnResponse) {
            doc.setCursor(nextPos);
          }
					*/
					updateCoqtopPane(goingDown, response);

					var name = Utils.getVernacName(request);
					if (name) {
						if (!_(namesPossiblyInScope).contains(name)) {
							namesPossiblyInScope.push(name);
						}
					}

					if (!Globals.activeProofTree) {
						if (response.focused.length === 1 && response.unfocused.length ===
							0
						) {
							createProofTree(response);
						}
					} else {
						// it is possible to start a proof within another proof,
						// stacking trees
						if (response.focused.length === 1 && response.unfocused.length ===
							0 && _(Utils.theoremStarters).contains(Utils.getVernac(request))
						) {
							Globals.activeProofTree.div.style("display", "none");
							Globals.activeProofTrees.push(activeProofTree);
							createProofTree(response);
						}
					}

					break;

				case 'Fail':

					// move proving and toprove back to unlocked
					var rProving = Globals.mProving.find();
					var rProved = Globals.mProved.find();
					var rUnlocked = Globals.mUnlocked.find();
					Editor.markProving(rProving.from, rProving.from);
					Editor.markToprove(rProving.from, rProving.from);
					Editor.markUnlocked(rProving.from, rUnlocked.to);
					Globals.doc.setCursor(rProving.from);
					Globals.cm.focus(); // somehow it gets unfocused sometimes
					updateCoqtopPane(goingDown, response);

					break;
			};

			Lecture.resizeCoqtopPanes();

			break;

	}
}

function rewindToPos(pos) {
	var rProved = Globals.mProved.find();
	if (positionIsBefore(rProved.to, pos)) {
		return Promise.resolve();
	} else {
		return onCtrlUp(false).then(function() {
			rewindToPos(pos);
		});
	}
}

function processToPos(pos) {
	var rToprove = Globals.mToprove.find();
	var rest = doc.getRange(rToprove.to, pos);
	if (Utils.coqTrim(rest) !== "") {
		onCtrlDown(false);
		processToPos(pos);
	}
}

module.exports = {
	"markRegion": markRegion,
	"markRegionDoc": markRegionDoc,
	"markProved": markProved,
	"markToprove": markToprove,
	"markProving": markProving,
	"markUnlocked": markUnlocked,
	"onCtrlDown": onCtrlDown,
	"onCtrlEnter": onCtrlEnter,
	"onCtrlUp": onCtrlUp,
	"onResponse": onResponse,
	"scrollIntoView": scrollIntoView,
	"updateCoqtopPane": updateCoqtopPane,
};
