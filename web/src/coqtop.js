/* @flow */

'use strict';

var Editor = require('./editor');
var Globals = require('./globals');
var Lecture = require('./lecture');
var PeaCoqResponse = require('./peacoqresponse');
var ProofTree = require('./prooftree');

var processingAsync: bool = false;

type PeaCoqRequest = {
	url: string;
	query: string;
	callback: (r: PeaCoqResponse) => void;
}

var asyncRequests: Array < PeaCoqRequest > = [];

/*
  This is the only function which does not return a promise. It is not to be
  called directly, use one of the async* methods below.
*/
function processAsyncRequests() {

	if (processingAsync) {
		return;
	}

	if (_(asyncRequests).isEmpty()) {
		return;
	}

	var request = asyncRequests.shift();
	var r = request.url;
	var q = request.query;
	var h = request.callback;
	if (r === 'query') {
		console.log(q);
	}
	processingAsync = true;
	Lecture.onRequestTriggered(r, q);
	var beforeTime = Date.now();

	$.ajax({
		type: 'POST',
		url: r,
		data: {
			query: q
		},
		async: true,
		error: function() {
			processingAsync = false;
			alert("Server did not respond!");
		},
		success: function(rawResponse) {
			var response = new PeaCoqResponse(rawResponse);

			var afterTime = Date.now();

			processingAsync = false;

			Editor.onResponse(r, q, response);
			if (Globals.activeProofTree) {
				Globals.activeProofTree.onResponse(r, q, response);
			}

			processAsyncRequests();

			h(response);

		}
	});

}

function asyncRequest(r: string, q: string): Promise {
	return new Promise(function(onFulfilled, onRejected) {
		asyncRequests.push({
			"url": r,
			"query": q,
			"callback": onFulfilled,
		});
		processAsyncRequests();
	});
}

function asyncQuery(q: string): Promise {
	return asyncRequest('query', q);
}

function asyncQueryAndUndo(q: string): Promise {
	return asyncRequest('queryundo', q);
}

function asyncUndo(): Promise {
	return asyncRequest('undo', '');
}

function asyncRevision(): Promise {
	return asyncRequest('revision', '');
}

function asyncRewind(delta: number): Promise {
	console.log('Rewind', delta);
	return asyncRequest('rewind', delta.toString());
}

function asyncLog(s: string): Promise {
	var time = "[" + new Date().toLocaleString() + "] ";
	return asyncRequest("log", time + s);
}

function asyncStatus(): Promise {
	return asyncRequest("status", "").then(function(response) {
		var msg = response.contents[0];
		var r = msg.match("^\\\((.*),(.*),(.*),\"(.*)\",\"(.*)\"\\\)$");
		var result = {
			"sections": r[1],
			"current": (r[2] === "Nothing") ? null : r[2].substring(5).replace(
				/"/g, ""),
			"currents": r[3],
			"label": +r[4],
			"proving": (r[5] === "1"),
			"response": response,
		};
		return result;
	});
}

function asyncCurrentLabel(): Promise {
	return asyncStatus()
		.then(function(status) {
			return status.label;
		});
}

function asyncResetCoq(): Promise {
	return asyncCurrentLabel()
		.then(function(label) {
			if (label > 0) {
				return asyncRewind(label - 1);
			} else {
				return Promise.resolve();
			}
		});
}

module.exports = {
	"asyncQuery": asyncQuery,
	"asyncQueryAndUndo": asyncQueryAndUndo,
	"asyncUndo": asyncUndo,
	"asyncRevision": asyncRevision,
	"asyncRewind": asyncRewind,
	"asyncLog": asyncLog,
	"asyncStatus": asyncStatus,
	"asyncCurrentLabel": asyncCurrentLabel,
	"asyncResetCoq": asyncResetCoq,
}
