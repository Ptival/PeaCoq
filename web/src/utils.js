/* @flow */

'use strict';

var Globals = require('./globals');
var Goal = require('./goal');

function delayPromise(time: number): (a: any) => Promise {
	return function(result) {
		return new Promise(function(onFulfilled, onRejected) {
			window.setTimeout(function() {
				onFulfilled(result);
			}, time);
		});
	}
}

function makeGoals(list: Array < Goal.PeaCoqRawGoal > ): Array < Goal > {
	return _(list)
		.map(function(elt) {
			return new Goal(elt);
		})
		.value();
}

function coqTrimLeft(s: string): string {
	var commentDepth = 0;
	var pos = 0;
	while (pos < s.length) {
		var sub = s.substring(pos);
		if (sub.startsWith("(*")) {
			commentDepth++;
			pos += 2;
		} else if (sub.startsWith("*)")) {
			commentDepth--;
			pos += 2;
		} else if (commentDepth > 0) {
			pos++;
		} else if (sub[0] === ' ' || sub[0] === '\n') {
			pos++;
		} else {
			return sub;
		}
	}
	return "";
}

// Some of this code has been borrowed from the ProofWeb project
// Their license is unclear, TODO make sure we can borrow, oops!
var delimiters = ['.'];

function my_index(str) {
	var index = +Infinity;
	_(delimiters).each(function(delimiter) {
		var pos = str.indexOf(delimiter);
		if (pos >= 0 && pos < index) {
			index = pos;
		}
	});
	if (index !== +Infinity) {
		return index;
	} else {
		return -1;
	}
}

function count(str: string, pat: string): number {
	var arr = str.split(pat);
	return (arr.length);
}

function coq_undot(str: string): string {
	str = str.replace(/[.][.][.]/g, '__.'); // emphasize the last dot of ...
	str = str.replace(/[.][.]/g, '__'); // hides .. in notations
	str = str.replace(/[.][a-zA-Z1-9_]/g, '__'); // hides qualified identifiers
	// hide curly braces that are implicit arguments
	str = str.replace(/\{((?:[^\.\}]|\.(?!\s))*)\}/g, "_$1_");
	// make other braces look like periods
	str = str.replace(/[\{\}]/g, ".");
	return str;
}

function coq_find_dot(str: string, toclose: number): number {
	var index = my_index(str);
	if (index == -1) {
		return index;
	}
	var tocheck = str.substring(0, index);
	var opened = count(tocheck, "(*") + toclose - count(tocheck, "*)");
	if (opened <= 0) {
		return index;
	} else {
		var newindex = coq_find_dot(str.substring(index + 1), opened);
		if (newindex == -1) return -1;
		return index + newindex + 1;
	}
}

var bullets: Array < string > = ["{", "}", "+", "-", "*"];

function next(str: string): number {
	// if the very next thing is one of {, }, +, -, *, it is the next
	var trimmed = coqTrimLeft(str);
	if (_(bullets).contains(trimmed[0])) {
		return str.length - trimmed.length + 1;
	}
	// otherwise, gotta find a dot
	return coq_find_dot(coq_undot(str), 0) + 1;
}

function coq_get_last_dot(str) {
	var modified = str;
	var index = -1;
	while (my_index(modified) >= 0) {
		index = my_index(modified);
		modified = modified.substring(0, index) + " " +
			modified.substring(index + 1);
	}
	return index;
}

function coq_find_last_dot(str, toopen) {
	var index = coq_get_last_dot(str);
	if (index == -1) {
		return index;
	}
	var tocheck = str.substring(index + 1);
	var closed = count(tocheck, "*)") + toopen - count(tocheck, "(*");
	if (closed <= 0) {
		return index;
	} else {
		var newindex = coq_find_last_dot(str.substring(0, index), closed);
		return newindex;
	}
}

function prev(str: string): number {
	// remove the last delimiter, since we are looking for the previous one
	var str = str.substring(0, str.length - 1);
	var lastDotPosition = coq_find_last_dot(coq_undot(str), 0);
	// now, it could be the case that there is a bullet after that dot
	var strAfterDot = str.substring(lastDotPosition + 1, str.length);
	var firstCharAfterDot = coqTrimLeft(strAfterDot)[0];
	if (_(bullets).contains(firstCharAfterDot)) {
		return lastDotPosition + 1 + strAfterDot.indexOf(firstCharAfterDot) + 1;
	}
	// otherwise, find the last dot
	return coq_find_last_dot(coq_undot(str), 0) + 1;
}

function scrollIntoView() {
	var cursorPos = Globals.doc.getCursor();
	Globals.cm.scrollIntoView({
		"from": Globals.cm.findPosV(cursorPos, -1, "line"),
		"to": Globals.cm.findPosV(cursorPos, +1, "line"),
	});
}

function outputError(error: Error): void {
	console.log(error, error.stack);
}

function stripWarning(s: string): string {
	return s.replace(
		/^Warning: query commands should not be inserted in scripts\n/g,
		""
	);
}

function stripComments(s) {
	var output = "";
	var commentDepth = 0;
	var pos = 0;
	while (pos < s.length) {
		var sub = s.substring(pos);
		if (sub.startsWith("(*")) {
			commentDepth++;
			pos += 2;
		} else if (sub.startsWith("*)")) {
			commentDepth--;
			pos += 2;
		} else if (commentDepth > 0) {
			pos++;
		} else {
			output += s[pos];
			pos++;
		}
	}
	return output;
}

function coqTrim(s: string): string {
	return stripComments(s).trim();
}

function coqTrimLeft(s: string): string {
	var commentDepth = 0;
	var pos = 0;
	while (pos < s.length) {
		var sub = s.substring(pos);
		if (sub.startsWith("(*")) {
			commentDepth++;
			pos += 2;
		} else if (sub.startsWith("*)")) {
			commentDepth--;
			pos += 2;
		} else if (commentDepth > 0) {
			pos++;
		} else if (sub[0] === ' ' || sub[0] === '\n') {
			pos++;
		} else {
			return sub;
		}
	}
	return "";
}

function coqTrimRight(s: string): string {
	var commentDepth = 0;
	var pos = s.length - 1;
	while (pos > 0) {
		var sub = s.substring(0, pos);
		var lastChar = sub[sub.length - 1];
		if (sub.endsWith("*)")) {
			commentDepth++;
			pos -= 2;
		} else if (sub.endsWith("(*")) {
			commentDepth--;
			pos -= 2;
		} else if (commentDepth > 0) {
			pos--;
		} else if (lastChar === ' ' || lastChar === '\n') {
			pos--;
		} else {
			return sub;
		}
	}
	return "";
}

var theoremStarters = [
	'CoFixpoint', 'Definition', 'Example', 'Fixpoint', 'Lemma', 'Theorem',
];

/*
 * TODO: OMG this is ugly, gotta make something better when I have time
 */
function splitAtFirstDelimiter(s) {
	var firstSpace = s.indexOf(' ');
	if (firstSpace === -1) {
		firstSpace = +Infinity;
	}
	var firstNewline = s.indexOf('\n');
	if (firstNewline === -1) {
		firstNewline = +Infinity;
	}
	var firstColon = s.indexOf(':');
	if (firstColon === -1) {
		firstColon = +Infinity;
	}
	var firstParen = s.indexOf('(');
	if (firstParen === -1) {
		firstParen = +Infinity;
	}
	var firstCurly = s.indexOf('{');
	if (firstCurly === -1) {
		firstCurly = +Infinity;
	}
	var firstDelimiter = Math.min(firstSpace, firstNewline, firstColon,
		firstParen, firstCurly);
	if (firstDelimiter === +Infinity) {
		return undefined;
	} else {
		return {
			"before": s.substring(0, firstDelimiter),
			"after": s.substring(firstDelimiter + 1),
		};
	}
}

function getVernac(s: string): string {
	var trimmed = coqTrim(s);
	var split = splitAtFirstDelimiter(trimmed);
	if (split === undefined) {
		return s; // untrimmed!
	} else {
		return split.before;
	}
}

// TODO: extract all the constructor names from an inductive definition
// Returns the name defined by a command, if any
function getVernacName(s: string): ? string {
	var trimmed = coqTrim(s);
	var split = splitAtFirstDelimiter(trimmed);
	if (split == undefined) {
		return undefined;
	}
	if (!_(theoremStarters).contains(split.before)) {
		return undefined;
	}
	split = splitAtFirstDelimiter(split.after);
	if (split == undefined) {
		return undefined;
	}
	return split.before;
}

module.exports = {
	"coqTrim": coqTrim,
	"coqTrimLeft": coqTrimLeft,
	"coqTrimRight": coqTrimRight,
	"delayPromise": delayPromise,
	"getVernac": getVernac,
	"getVernacName": getVernacName,
	"makeGoals": makeGoals,
	"next": next,
	"outputError": outputError,
	"prev": prev,
	"scrollIntoView": scrollIntoView,
	"stripWarning": stripWarning,
	"theoremStarters": theoremStarters,
}
