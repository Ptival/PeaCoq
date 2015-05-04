/* @flow */

'use strict';

type PeaCoqRawGoal = {
	gId: number;
	gHyps: Array < Object > ;
	gGoal: Object;
}

class Goal {
	gId: number;
	gHyps: Array < Hypothesis > ;
	gGoal: Goal;
	constructor(g: PeaCoqRawGoal) {
		this.gId = g.gId;
		this.gHyps = g.gHyps;
		this.gGoal = g.gGoal;
	}
}

function extractGoal(gGoal: Object) {
	if (gGoal.hasOwnProperty("Left")) {
		gGoal = {
			"contents": gGoal.Left,
			"tag": "Raw",
		};
	} else {
		gGoal = gGoal.Right;
	}
	return gGoal;
}

function extractHypothesis(gHyp: Object) {

	if (gHyp.hasOwnProperty("Left")) {
		// this tries to approximate parsing...
		var matches = gHyp.Left.match(/^([\s\S]*) := ([\s\S]*) : ([\s\S]*)$/);
		if (matches !== null) {
			gHyp = {
				"hName": matches[1],
				"hValue": {
					"contents": matches[2],
					"tag": "Raw"
				},
				"hType": {
					"contents": matches[3],
					"tag": "Raw"
				},
			};
		} else {
			matches = gHyp.Left.match(/^([\s\S]*) : ([\s\S]*)$/);
			gHyp = {
				"hName": matches[1],
				"hValue": null,
				"hType": {
					"contents": matches[2],
					"tag": "Raw"
				},
			};
		}
		if (matches == null) {
			console.log("could not extract hypothesis", gHyp);
		}

	} else {
		gHyp = gHyp.Right;
	}

	return gHyp;

}

module.exports = Goal;
