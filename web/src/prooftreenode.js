/* @flow */

'use strict';

var ProofTree = require('./prooftree');

class ProofTreeNode {

	depth: number;
	id: number;
	//parent: ? ProofTreeNode;
	proofTree: ProofTree.ProofTree;
	solved: bool;
	x: number;
	y: number;

	/*
	We preemptively fill the [parent] and [depth] fields because D3 will only fill
	them for the visible ProofTreeNodes of the tree, while some algorithms require it
	before a ProofTreeNode has ever been visible.
	*/
	constructor(proofTree: ProofTree.ProofTree) {
		this.id = _.uniqueId();
		this.proofTree = proofTree;
		this.depth = parent ? parent.depth + 1 : 0;
		this.solved = false;
	}

	isCurNode(): bool {
		return this.id === this.proofTree.curNode.id;
	}

	isSolved(): bool {
		return this.solved;
	}

}

module.exports = ProofTreeNode;
