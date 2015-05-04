/* @flow */

'use strict';

var Goal = require('./goal');
var Utils = require('./utils');

type ResponseContents = {
	tag: string;
	contents: Array < string > ;
}

type UnfocusedItem = {
	goalsBefore: Array < Goal > ;
	goalsAfter: Array < Goal > ;
}

declare class PeaCoqRawResponse {
	rGoals: {
		focused: Array < Object > ;
		unfocused: Array < Object > ;
	};
	rResponse: ResponseContents;
}

class PeaCoqResponse {
	tag: string;
	contents: Array < string > ;
	focused: Array < Goal > ;
	unfocused: Array < UnfocusedItem > ;

	constructor(r: PeaCoqRawResponse) {
		console.log(r.rResponse);
		this.tag = r.rResponse.tag;
		this.contents = r.rResponse.contents;
		this.focused = Utils.makeGoals(r.rGoals.focused);
		this.unfocused = _(r.rGoals.unfocused)
			.map(function(elt) {
				var goalsBefore = elt[0];
				var goalsAfter = elt[1];
				return {
					"goalsBefore": Utils.makeGoals(goalsBefore),
					"goalsAfter": Utils.makeGoals(goalsAfter),
				};
			})
			.value();
	}


}

module.exports = PeaCoqResponse;
