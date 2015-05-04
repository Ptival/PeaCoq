/* @flow */

'use strict';

var PeaCoqResponse = require('./peacoqresponse');
var ProofTree = require('./prooftree');
var ProofTreeNode = require('./prooftreenode');
var TacticGroupNode = require('./tacticgroupnode');
var TacticNode = require('./tacticnode');

class GoalNode extends ProofTreeNode {

	closedBraces: number;
	hyps: Array < Hypothesis > ;
	openBraces: number;
	//parent: ? TacticNode;
	// this should be updated on every visit with the last response
	response: PeaCoqResponse;
	tacticGroups: Array < TacticGroupNode > ;
	tacticIndex: number;

	constructor(proofTree: ProofTree, parentTactic: ? TacticNode, response :
		PeaCoqResponse, index: number) {
		//var goal = response.focused[index];
		//ProofTreeNode.call(this, proofTree);
		/*
		var goalTerm = extractGoal(goal.gGoal);
		this.hyps = _(goal.gHyps).map(extractHypothesis).value();
		this.ndx = index + 1; // used in Focus, Coq uses 1-index
		this.gid = goal.gId;
		this.goalTerm = goalTerm;
		this.goalString = showTermText(goalTerm);
		this.tacticGroups = [
			new TacticGroupNode(proofTree, this, userTacticsGroupName)
		];
		this.tacticIndex = 0;
		this.parentTactic = parentTactic;
		this.response = response;
		this.openBraces = 0;
		this.closedBraces = 0;
		*/
	}

	getViewChildren(): Array < TacticGroupNode > {
		if (this.isSolved()) {
			return [];
		}
		// TODO: reimplement this
		return [];
	}
}

module.exports = GoalNode;
