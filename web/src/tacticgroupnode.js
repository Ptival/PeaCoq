/* @flow */

'use strict';

var GoalNode = require('./goalnode');
var ProofTree = require('./prooftree');
var ProofTreeNode = require('./prooftreenode');
var TacticNode = require('./tacticnode');

class TacticGroupNode extends ProofTreeNode {
	name: string;
	parent: GoalNode;
	tactics: Array < TacticNode > ;
	tacticIndex: number;
	constructor(proofTree: ProofTree, parent: GoalNode, name: string) {
		ProofTreeNode.call(this, proofTree);
		this.name = name;
		this.tactics = [];
		this.tacticIndex = 0;
	}
}

module.exports = TacticGroupNode;
