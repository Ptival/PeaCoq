/* @flow */

'use strict';

var Coqtop = require('./coqtop');
var FakeNode = require('./fakenode');
var Globals = require('./globals');
var GoalNode = require('./goalnode');
var PeaCoqResponse = require('./peacoqresponse');
var ProofTreeNode = require('./prooftreenode');
var TacticGroupNode = require('./tacticgroupnode');

class ProofTree {

	anchor: D3Selection;
	curNode: ProofTreeNode;
	diagonal: (pair: {
		source: ProofTreeNode;
		target: ProofTreeNode;
	}) => string;
	diffLayer: D3Selection;
	div: D3Selection;
	height: number;
	linkLayer: D3Selection;
	rectLayer: D3Selection;
	rootNode: ProofTreeNode;
	svg: D3Selection;
	svgId: number;
	tactics: (p: ProofTree) => Array < Group > ;
	textLayer: D3Selection;
	tipsLayer: D3Selection;
	tree: D3Tree;
	viewport: D3Selection;
	width: number;
	xFactor: number;

	constructor(anchor: Element, width: number, height: number): void {
		this.anchor = d3.select(anchor);
		this.width = width;
		this.height = height;
		this.svgId = _.uniqueId();
		this.xFactor = this.width;

		this.tree = d3.layout.tree()
			.children(function(node: ProofTreeNode): Array < ProofTreeNode > {
				// fake ProofTreeNodes are used to trick the layout engine into spacing
				// childrenless ProofTreeNodes appropriately
				if (node.constructor === FakeNode) {
					return [];
				}
				var viewChildren = ProofTreeNode.getViewChildren();
				// in order to trick d3 into displaying tactics better add fake
				// children to tactic ProofTreeNodes that solve their goal
				if (node.constructor === TacticGroupNode && viewChildren.length ===
					0) {
					return [new FakeNode()];
				}
				return viewChildren;
			})
			.separation(function(d: ProofTreeNode) {
				return 1 / (1 + d.depth * d.depth * d.depth);
			});

		this.diagonal = d3.svg
			.diagonal()
			.projection(function(d) {
				return [d.y, d.x];
			});

		d3.select("body")
			.on("keydown", function() {
				// capture events only if we are in proof mode
				if ($(":focus").size() === 0) {
					self.keydownHandler();
				}
			});

		this.div = this.anchor
			.insert("div", ":first-child")
			.attr("id", "pt-" + this.svgId)
			.classed("prooftree", true);

		this.svg = this.div
			.insert("svg", ":first-child")
			.classed("svg", true)
			.attr("id", "svg-" + this.svgId)
			// necessary for the height to be exactly what we set
			.attr("display", "block")
			.style("width", this.width + "px")
			.style("height", this.height + "px")
			//.attr("focusable", true)
			// this creates a blue outline that changes the width weirdly
			//.attr("tabindex", 0)
		;

		this.viewport =
			this.svg
			.append("g")
			.attr("id", "viewport") // for SVGPan.js
			.attr("class", "viewport")
			.attr("transform",
				"translate(" + self.goalWidth + ", " + 0 + ")"
			);

		// Note : the order of these influence the display:
		// first = bottom, last = top
		this.linkLayer = this.viewport.append("g").attr("id", "link-layer");
		this.rectLayer = this.viewport.append("g").attr("id", "rect-layer");
		this.diffLayer = this.viewport.append("g").attr("id", "diff-layer");
		this.textLayer = this.viewport.append("g").attr("id", "text-layer");
		this.tipsLayer = this.viewport.append("g").attr("id", "tips-layer");

		if (Globals.svgPanEnabled) {
			this.svg
				.insert("script", ":first-child")
				.attr("xlink:href", "SVGPan.js");
		}

		Globals.activeProofTree = this;

	}

	getCurrentGoal(): GoalNode {
		return this.curNode;
	}

	getFocus() {

	}

	hInit(response: PeaCoqResponse): bool {

		var self = this;

		if (response.tag == 'Fail') {
			console.log(response.contents);
			/*
			if (this.onError !== undefined) {
			    this.onError(this, response.rResponse.contents);
			}
			*/
			return false;
		}

		// There should only be one goal at that point
		this.rootNode = new GoalNode(this, undefined, response, 0);

		// doesn't matter much when this is done, so no chaining
		/*
    Coqtop.asyncStatus()
      .then(function(status) {
        self.rootNode.label = status.label;
      });
*/

		this.curNode = this.rootNode;

		// this is now done later once 'Proof.' has been processed
		//this.refreshTactics();

		this.update();

		return true;

	}

	newAlreadyStartedTheorem(
		lastResponse: PeaCoqResponse,
		tactics: (p: ProofTree) => Array < Group >
	) {

		var self = this;

		this.tactics = tactics;

		// hide previous proof result if any, show svg if hidden
		this.svg.style("display", "");

		var success = false;

		self.hInit(lastResponse);

		//this.getFocus();
		//this.svg.on("click")();

	}

	onResponse(request: string, query: string, response: PeaCoqResponse) {

	}

	onUndo(fromUser: bool, undone: string, response: PeaCoqResponse) {

	}

	refreshTactics() {

	}

	resize(width: number, height: number) {

	}

	update() {

	}

}

module.exports = ProofTree;
