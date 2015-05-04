/* @flow */

'use strict';

var GoalNode = require('./goalnode');
var PeaCoqResponse = require('./peacoqresponse');
var ProofTree = require('./prooftree');
var ProofTreeNode = require('./prooftreenode');
var TacticGroupNode = require('./tacticgroupnode');

class TacticNode extends ProofTreeNode {

	goalIndex: number;
	goals: Array < GoalNode > ;
	parent: TacticGroupNode;
	tactic: string;

	constructor(proofTree: ProofTree, parent: TacticGroupNode,
		tactic: string, response: PeaCoqResponse) {

		var self = this;

		ProofTreeNode.call(this, proofTree);

		this.parent = parent;
		this.tactic = tactic;

		var focusedBefore = parent.parent.response.focused;
		var focusedAfter = response.focused;

		var unfocusedBefore = parent.parent.response.unfocused;
		var unfocusedAfter = response.unfocused;

		var remainingSubgoals;
		if (_.isEqual(unfocusedAfter, unfocusedBefore)) {
			if (focusedBefore.length > 1 && focusedAfter[0].gId === focusedBefore[1].gId) {
				remainingSubgoals = [];
			} else {
				var focusDelta = focusedAfter.length - focusedBefore.length;
				remainingSubgoals = response.focused.slice(0, focusDelta + 1);
			}
		} else {
			remainingSubgoals = [];
		}

		this.goals = _(remainingSubgoals).map(function(goal, index: number) {
			return new GoalNode(proofTree, self, response, 0); //index);
		}).value();
		this.goalIndex = 0;
	}

}

module.exports = TacticNode;
