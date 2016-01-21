
// TODO: add #loading to HTML

// TODO: fix asyncLog and uncomment calls to it

/* 0 is the active tree, rest is stack of background ones*/
let proofTrees: ProofTree[] = [];
let svgPanEnabled: boolean = false;
let nodeVSpacing = 10;
let nodeStroke = 2;
let rectMargin = { top: 2, right: 8, bottom: 2, left: 8 };
let animationDuration = 200;
let keyboardDelay = 100;
let keyboardPaused = false;

let diffRed = "#EE8888";
let diffGreen = "#88EE88";
let diffBlue = "#8888EE";
let diffOrange = "#FFB347";
let diffOpacity = 0.75;
let goalBodyPadding = 4;

$(document).ready(() => {
  peaCoqAddHandlers.push(proofTreeOnAdd);
  peaCoqGetContextHandlers.push(proofTreeOnGetContext);
  peaCoqGoalHandlers.push(proofTreeOnGoal);
  peaCoqStatusHandlers.push(proofTreeOnStatus);
});

function proofTreeOnAdd(s: string, r: AddReturn): void {
  console.log("TODO, proofTreeOnAdd", s, r);
}

function proofTreeOnGetContext(c: PeaCoqContext): void {
  if (proofTrees.length === 0) { return; }
  let activeProofTree = proofTrees[0];
  if (activeProofTree.curNode === undefined) {
    let g = new GoalNode(activeProofTree, undefined, c[0]);
  }
}

function proofTreeOnGoal(g: Goals): void {
}

function proofTreeOnStatus(s: Status): void {
  // hopefully we are always at most 1 tree late
  if (proofTrees.length + 1 === s.statusAllProofs.length) {
    // we are behind on the number of proof trees, create one
    let pt = new ProofTree(
      s.statusProofName,
      $("#prooftree")[0],
      $(window).width(),
      $("#prooftree").height(),
      function() { $("#loading").css("display", ""); },
      function() { $("#loading").css("display", "none"); }
      );
    proofTrees.unshift(pt);
    return;
  }
  // multiple trees might have been finished at once?
  while (proofTrees.length > s.statusAllProofs.length) {
    proofTrees.shift();
  }
  if (proofTrees.length !== s.statusAllProofs.length) {
    alert("Error: we are missing multiple proof trees!")
  }
}

function assert(condition: boolean, message: string): void {
  if (!condition) {
    alert("Assertion failed: " + message);
    throw message || "Assertion failed";
  }
}

type Hypothesis = {
  div: HTMLElement;
  hName: string;
  hValue: string;
  hType: string;
}

function parseSVGTransform(a: string): any {
  let b = {};
  let m = a.match(/(\w+\((\-?\d+\.?\d*,? ?)+\))+/g);
  for (let i in m) {
    let c = m[i].match(/[\w\.\-]+/g);
    b[c.shift()] = c;
  }
  return b;
}

type XY = { x: number; y: number; }
function swapXY(r: any): any {
  return { "x": r.y, "y": r.x };
}

type ProofTreeLink = d3.svg.diagonal.Link<ProofTreeNode>;

type TacticGroup = {
  name: string;
  tactics: string[];
}

type WorklistItem = () => Promise<TacticGroup[]>;

class ProofTree {
  anchor: d3.Selection<HTMLElement>;
  /* whatever the client wants to store as meta-data */
  clientState: Object;
  curNode: GoalNode;
  descendantsOffset: number;
  diagonal: d3.svg.Diagonal<ProofTreeLink, ProofTreeNode>;
  goalWidth: number;
  height: number;
  keydownHandler: () => void;
  name: string;
  onEndProcessing: () => void;
  onStartProcessing: () => void;
  paused: boolean;
  tacticWidth: number;
  /* true until the user uses their mouse */
  usingKeyboard: boolean;
  rootNode: ProofTreeNode;
  svgId: string;
  tactics: () => TacticGroup[];
  tacticsWorklist: WorklistItem[];
  tree: d3.layout.Tree<ProofTreeNode>;
  viewportX: number;
  viewportY: number;
  width: number;
  xFactor: number;
  yFactor: number;

  div: d3.Selection<HTMLElement>;
  svg: d3.Selection<HTMLElement>;
  viewport: d3.Selection<HTMLElement>;
  linkLayer: d3.Selection<HTMLElement>;
  rectLayer: d3.Selection<HTMLElement>;
  diffLayer: d3.Selection<HTMLElement>;
  textLayer: d3.Selection<HTMLElement>;
  tipsLayer: d3.Selection<HTMLElement>;

  constructor(
    name: string,
    anchor: HTMLElement, width: number, height: number,
    onStartProcessing: () => void, onEndProcessing: () => void
    ) {
    let self = this;

    this.name = name;
    this.anchor = d3.select(anchor);
    this.width = width;
    this.height = height;
    this.onStartProcessing = onStartProcessing;
    this.onEndProcessing = onEndProcessing;

    this.paused = false;
    this.svgId = _.uniqueId();
    this.xFactor = this.width;
    this.yFactor = this.height;
    this.clientState = {};
    this.usingKeyboard = true; // true until the user moves their mouse
    this.goalWidth = computeGoalWidth(this.width);
    this.tacticWidth = computeTacticWidth(this.width);

    this.tree = d3.layout.tree<ProofTreeNode>()
      .children(
      (node: ProofTreeNode, index: number) => {
        // fake nodes are used to trick the layout engine into spacing
        // childrenless nodes appropriately
        if (node.isFake) { return []; }
        let viewChildren = node.getViewChildren();
        if (viewChildren === undefined) {
          throw node;
        }
        // in order to trick d3 into displaying tactics better add fake
        // children to tactic nodes that solve their goal
        if (node.isTacticish() && viewChildren.length === 0) {
          return [new FakeNode()];
        }
        return viewChildren;
      })
      .separation(
      (d) => {
        // TODO: now that I put fake nodes, still need this?
        // TODO: this just won't work, need invisible children
        // for tactics without children
        return 1 / (1 + (d.depth * d.depth * d.depth));
      })
    ;

    this.diagonal = d3.svg
      .diagonal<ProofTreeNode>()
      .projection(function(d) { return [d.y, d.x]; })
    ;

    d3.select("body")
      .on("keydown", function() {
      // capture events only if we are in proof mode
      if ($(":focus").length === 0) {
        self.keydownHandler();
      }
    })
    ;

    this.div = this.anchor
      .insert("div", ":first-child")
      .attr("id", "pt-" + this.svgId)
      .classed("prooftree", true)
    ;

    this.svg = this.div
      .insert("svg", ":first-child")
      .classed("svg", true)
      .attr("id", "svg-" + this.svgId)
    // necessary for the height to be exactly what we set
      .attr("display", "block")
      .style("width", this.width + "px")
      .style("height", this.height + "px")
    // also need these as attributes for svg_todataurl
      .attr("width", this.width + "px")
      .attr("height", this.height + "px")
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
      )
    ;

    // note: the order of these influence the display
    // from bottom layers
    this.linkLayer = this.viewport.append("g").attr("id", "link-layer");
    this.rectLayer = this.viewport.append("g").attr("id", "rect-layer");
    this.diffLayer = this.viewport.append("g").attr("id", "diff-layer");
    this.textLayer = this.viewport.append("g").attr("id", "text-layer");
    this.tipsLayer = this.viewport.append("g").attr("id", "tips-layer");
    // to top layers

    if (svgPanEnabled) {
      this.svg.insert("script", ":first-child").attr("xlink:href", "SVGPan.js");
    }

  }

  commonAncestor(n1: ProofTreeNode, n2: ProofTreeNode): ProofTreeNode {
    if (n1.id === this.rootNode.id || n2.id === this.rootNode.id) {
      return this.rootNode;
    }
    if (n1.id === n2.id) { return n1; }
    if (n1.depth < n2.depth) {
      return this.commonAncestor(n1, n2.parent);
    } else if (n1.depth > n2.depth) {
      return this.commonAncestor(n1.parent, n2);
    } else {
      return this.commonAncestor(n1.parent, n2.parent);
    }
  }

  curGoal(): GoalNode {
    return getClosestGoal(this.curNode);
  }

  findOrCreateGroup(goalNode: GoalNode, groupName: string): TacticGroupNode {
    let found = _(goalNode.tacticGroups)
      .find(function(tacticGroup) {
      return tacticGroup.name === groupName;
    })
      ;
    if (found !== undefined) { return found; }
    // else, create it
    let groupNode = new TacticGroupNode(this, goalNode, groupName);
    goalNode.tacticGroups.push(groupNode);
    return groupNode;
  }

  getFocus() {
    $(":focus").blur();
  }

  getFocusedGoal(): GoalNode {
    let focusedChild = this.curNode.getFocusedChild();
    if (focusedChild !== undefined) {
      //if (focusedChild instanceof GoalNode) { return focusedChild; }
      let focusedGrandChild = focusedChild.getFocusedChild();
      if (focusedGrandChild !== undefined) {
        return focusedGrandChild;
      }
    }
    return undefined;
  }

  isCurGoal(n: ProofTreeNode): boolean {
    return n.id === this.curGoal().id;
  }

  isCurGoalChild(n: ProofTreeNode): boolean {
    return hasParent(n) && this.isCurGoal(n.parent);
  }

  isCurGoalGrandChild(n: ProofTreeNode): boolean {
    return hasParent(n) && this.isCurGoalChild(n.parent);
  }

  isCurNode(n: ProofTreeNode): boolean { return n.id === this.curNode.id; }

  isCurNodeChild(n: ProofTreeNode): boolean {
    return hasParent(n) && this.isCurNode(n.parent);
  }

  isCurNodeGrandChild(n: ProofTreeNode): boolean {
    return hasParent(n) && this.isCurNodeChild(n.parent);
  }

  isCurNodeParent(n: ProofTreeNode): boolean {
    return hasParent(this.curNode) && this.curNode.parent.id === n.id;
  }

  isCurNodeSibling(n: ProofTreeNode): boolean {
    return !this.isCurNode(n) && hasParent(n) && this.isCurNodeParent(n.parent);
  }

  isRootNode(n: ProofTreeNode): boolean {
    return n.id === this.rootNode.id;
  }

  linkWidth(d: ProofTreeLink): string {
    let src = d.source;
    let tgt = d.target;
    let thin = "2px";
    let thick = "5px";
    // if the user uses his mouse, highlight the path under hover
    /*
    if (!this.usingKeyboard) {
        if (this.hoveredNode === undefined) {
            return thin;
        } else {
            if (this.isCurNode(src)) {
                if (sameNode(tgt, this.hoveredNode)) { return thick; }
                else if (!hasParent(this.hoveredNode)) { return thin; }
                else if (sameNode(tgt, this.hoveredNode.parent)) {
                    return thick;
                }
                else { return thin; }
            } else if (this.isCurNodeChild(src)) {
                if (sameNode(tgt, this.hoveredNode)) { return thick; }
                else { return thin; }
            } else {
                return thin;
            }
        }
    }
    */
    // if the user uses his keyboard, highlight the focused path
    if (this.curNode instanceof GoalNode) {
      let focusedChild = this.curNode.getFocusedChild();
      if (focusedChild === undefined) { return thin; }
      if (this.isCurNode(src) && focusedChild.id === tgt.id) { return thick; }
      // we want to thicken the path to the focused subgoal
      let focusedGrandChild = focusedChild.getFocusedChild();
      if (focusedGrandChild === undefined) { return thin; }
      if (focusedChild.id == src.id && focusedGrandChild.id === tgt.id) {
        return thick;
      }
      return thin;
    } else if (this.curNode.isTacticish()) {
      let focusedChild = this.curNode.getFocusedChild();
      if (focusedChild !== undefined && tgt.id === focusedChild.id) {
        return thick;
      }
      return thin;
    } else {
      throw this.curNode;
    }
  }

  processTactics(): Promise<any> {

    /*
      every time curNode is changed, the tacticsWorklist should be
      flushed, so that [runTactic] can reliably add the results of running
      the tactic to the current node
    */

    this.onStartProcessing();

    if (_(this.tacticsWorklist).isEmpty()) {
      this.onEndProcessing();
      return Promise.resolve();
    }

    let promiseSpark = this.tacticsWorklist.shift();

    return promiseSpark()
    // delay for testing purposes
    //.then(delayPromise(0))
      .then(this.processTactics.bind(this))
      .catch(outputError);

  }

  refreshTactics(): void {

    //if (focusedOnEditor) { return; }

    let self = this;
    let curNode = this.curNode;

    let tacticsAndGroups = this.tactics();

    /*
      _(this.tactics())
        .groupBy(function(elt) {
        if ($.type(elt) === "string") {
          return "tactics";
        } else {
          return "groups";
        }
      })
        .value()
      ;

      // TODO: there should be no tactics!
      let groups = tacticsAndGroups.groups;
      */

    let groupSparks = _(tacticsAndGroups)
      .map(function(group) {
      let groupNode: TacticGroupNode = self.findOrCreateGroup(curNode, group.name);
      return (
        _(group.tactics)
          .filter(
          (tactic) => {
            return (
              !_(groupNode.tactics)
                .some(function(node) {
                return (node.tactic === tactic);
              })
              );
          })
          .map(
          (tactic) => {
            return function() {
              return self.runTactic(tactic, groupNode);
            }
          })
          .flatten(true)
          .value()
        );
    })
      .flatten<() => Promise<any>>(true)
      .value()
      ;

    // flushes the worklist and add the new sparks
    this.tacticsWorklist = groupSparks;

    //console.log("REPOPULATING TACTICS WORKLIST", this.tacticsWorklist);

    this.processTactics();
  }

  resetSVGTransform(): void {
    let m = parseSVGTransform(this.viewport.attr('transform'));
    if (m.hasOwnProperty('matrix')) {
      m = m.matrix;
      this.viewport.attr('transform',
        'matrix(1' + ',' + m[1] + ',' + m[2]
        + ', 1' + ',' + m[4] + ',' + m[5] + ')')
      ;
    }
  }

  runTactic(t, groupToAttachTo) {

    let self = this;

    let parentGoal = getClosestGoal(groupToAttachTo);
    let parentGoalRepr = goalNodeUnicityRepr(parentGoal);

    // if we correctly stored the last response in [parentGoal], we don't need
    // to query for status at this moment
    let beforeResponse = parentGoal.response;

    $("#loading-text").text(nbsp + nbsp + "Trying " + t);

    return asyncQueryAndUndo(t)
    //.then(delayPromise(0))
      .then(function(response) {
      if (isGood(response)) {

        let unfocusedBefore = getResponseUnfocused(beforeResponse);
        let unfocusedAfter = getResponseUnfocused(response);
        let newChild = new TacticNode(
          self,
          groupToAttachTo,
          t,
          response
          );

        // only attach the newChild if it produces something
        // unique from existing children
        let newChildRepr = tacticNodeUnicityRepr(newChild);

        let resultAlreadyExists =
          _(parentGoal.getTactics()).some(function(t) {
            return t.tactic === newChild.tactic;
            //return (tacticNodeUnicityRepr(t) === newChildRepr);
          })
          ;

        let tacticIsUseless =
          (newChild.goals.length === 1)
          && (goalNodeUnicityRepr(newChild.goals[0])
            === parentGoalRepr)
          ;

        if (!resultAlreadyExists && !tacticIsUseless) {
          groupToAttachTo.addTactic(newChild);
          self.update();
        }

      } else {

        //console.log("Bad response for", t, response);

      }

    })
      .catch(outputError);

  }

  shiftNextByTacticGroup(n) {
    if (this.paused) { return; }
    let self = this;
    if (n.solved) { return; }
    let viewChildren = n.getViewChildren();
    if (n instanceof GoalNode) {
      if (n.tacticIndex + 1 < viewChildren.length) {
        n.tacticIndex++;
        //asyncLog("DOWNGROUP " + nodeString(viewChildren[n.tacticIndex]));
        self.update();
      }
    } else {
      throw n;
    }
  }

  shiftPrevByTacticGroup(n) {
    if (this.paused) { return; }
    let self = this;
    if (n.solved) { return; }
    if (n instanceof GoalNode) {
      if (n.tacticIndex > 0) {
        n.tacticIndex--;
        //asyncLog("UPGROUP " + nodeString(n.getViewChildren()[n.tacticIndex]));
        self.update();
      }
    } else {
      throw n;
    }
  }

  update(): Promise<{}> {

    //if (focusedOnEditor) { return Promise.resolve(); }

    let self = this;

    return new Promise(function(onFulfilled, onRejected) {

      // shorter name, expected to stay constant throughout
      let curNode = self.curNode;

      assert(curNode instanceof GoalNode, "curNode instanceof GoalNode");

      // if the viewpoint has been zoomed, cancel the zoom so that the computed
      // sizes are correct
      self.resetSVGTransform();

      let nodes = self.tree.nodes(self.rootNode);
      // now get rid of the fake nodes used for layout
      _(nodes)
        .each(function(node) {
        if (node.isTacticish() && node.getViewChildren().length === 0) {
          node.children = [];
        }
      });
      nodes = _(nodes)
        .filter(function(node) { return node instanceof FakeNode; })
        .value()
      ;
      let links = self.tree.links(nodes);

      // we build the foreignObject first, as its dimensions will guide the others
      let textSelection = self.textLayer
        .selectAll(function() {
        return this.getElementsByTagName("foreignObject");
      })
        .data(nodes, function(d) { return d.id || (d.id = _.uniqueId()); })
        ;

      // D3 populates the children field with undefined when no children
      // it makes my life easier to instead put an empty list there
      textSelection
        .each(function(d) {
        if (!d.hasOwnProperty("children")) { d.children = []; }
      })
      ;

      let textEnter = textSelection.enter()
        .append("foreignObject")
        .classed("monospace", true)
      // the goal nodes need to be rendered at fixed width goalWidth
      // the tactic nodes will be resized to their actual width later
        .attr("width", function(d) {
        return d instanceof GoalNode ? self.goalWidth : self.tacticWidth;
      })
        ;

      textEnter
        .append("xhtml:body")
      //.classed("svg", true)
        .style("margin", 0) // keep this line for svg_datatourl
        .style("padding", function(d) {
        return d instanceof GoalNode ? goalBodyPadding + "px" : "0px 0px";
      })
        .style("background-color", "rgba(0, 0, 0, 0)")
      // should make it less painful on 800x600 videoprojector
      // TODO: fix computing diffs so that zooming is possible
        .style("font-size", (self.width < 1000) ? "12px" : "14px")
        .style("font-family", "monospace")
        .each(function(d) {
        let jqBody = $(d3.select(this).node());
        let jQContents;
        if (d instanceof TacticNode) {
          d.span = $("<div>")
            .addClass("tacticNode")
            .css("padding", "4px")
            .css("text-align", "center")
            .text(d.tactic);
          jQContents = d.span;
        } else if (d instanceof TacticGroupNode) {
          return; // needs to be refreshed on every update, see below
        } else if (d instanceof GoalNode) {
          jQContents = makeGoalNodePre();
          _(d.hyps).each(function(h) {
            let jQDiv = $("<div>")
              .html(showHypothesis(h))
              .attr("id", _.uniqueId())
              ;
            h.div = jQDiv[0];
            jQContents.append(h.div);
          });
          jQContents.append(makeContextDivider());
          d.goalSpan = $("<div>").html(showTerm(d.goalTerm));
          jQContents.append(d.goalSpan);
        } else {
          throw d;
        }
        jqBody.append(jQContents);
      })
      ;

      textSelection
      // the tactic groups need to be updated every time
        .each(function(d) {
        let jqBody = $(d3.select(this).select("body").node());
        let jQContents;
        if (d instanceof TacticGroupNode) {
          let focusedTactic = d.tactics[d.tacticIndex];
          let nbTactics = d.tactics.length;
          d.span = $("<div>")
            .addClass("tacticNode")
            .css("padding", "4px")
            .css("text-align", "center")
          ;

          // prepend a tactic node selector if necessary
          if (nbTactics > 1) {

            if (d.tacticIndex > 0) {
              d.span.append(
                $("<a>")
                  .attr("href", "#")
                  .text('◀')
                  .click(function(e) {
                  e.stopImmediatePropagation();
                  d.shiftPrevInGroup();
                })
                );
            } else {
              d.span.append(nbsp);
            }

            d.span.append(
              '[' + (d.tacticIndex + 1) + '/' + d.tactics.length + ']'
              );

            if (d.tacticIndex < d.tactics.length - 1) {
              d.span.append(
                $("<a>")
                  .attr("href", "#")
                  .text('▶')
                  .click(function(e) {
                  e.stopImmediatePropagation();
                  d.shiftNextInGroup();
                })
                );
            } else {
              d.span.append(nbsp);
            }

            d.span.append($("<br>"));

          }

          d.span.append(
            focusedTactic.tactic
            );

          jQContents = d.span;
          jqBody.empty();
          jqBody.append(jQContents);
        } else if (d instanceof GoalNode) {
          jQContents = makeGoalNodePre();
          _(d.hyps).each(function(h) {
            let jQDiv = $("<div>")
              .html(showHypothesis(h))
              .attr("id", _.uniqueId())
              ;
            h.div = jQDiv[0];
            jQContents.append(h.div);
          });

          jQContents.append(makeContextDivider());
          d.goalSpan = $("<div>").html(showTerm(d.goalTerm));
          jQContents.append(d.goalSpan);
          jqBody.empty();
          jqBody.append(jQContents);
        }
      })
        .each(function(d) {
        let nodeDOM = d3.select(this).node();
        self.updateNodeMeasures(nodeDOM, d);
      })
      // preset the width to update measures correctly
        .attr("width", function(d) {
        return d instanceof GoalNode ? self.goalWidth : self.tacticWidth;
      })
        .attr("height", 0)
        .each(function(d) {
        let nodeDOM = d3.select(this).node().firstChild;
        self.updateNodeMeasures(nodeDOM, d);
      })
      ;

      // Now that the nodes have a size, we can compute the factors

      let curGoal = self.curGoal();
      let visibleChildren = _(curGoal.getViewChildren());
      let visibleGrandChildren = _(curGoal.getViewGrandChildren());
      let emptyNodeArray: Array<ProofTreeNode> = [];
      let visibleNodes = _(emptyNodeArray);
      if (hasParent(curGoal)) {
        visibleNodes = visibleNodes.concat([curGoal.parent]);
      }
      visibleNodes = visibleNodes.concat([curGoal]);
      visibleNodes = visibleNodes.concat(visibleChildren.value());
      visibleNodes = visibleNodes.concat(visibleGrandChildren.value());

      // xFactor is now fixed, so that the user experience is more stable
      if (self.rootNode.children === undefined || self.rootNode.children.length === 0) {
        self.xFactor = self.width;
      } else {
        let xDistance = nodeX(self.rootNode.children[0]) - nodeX(self.rootNode);
        /* width = 4 * xDistance * xFactor */
        self.xFactor = self.width / (4 * xDistance);
      }

      /*
        we want all visible grand children to be apart from each other
        i.e.
        ∀ a b, yFactor * | a.y - b.y | > a.height/2 + b.height/2 + nodeVSpacing
        we also want all visible children to be apart from each other (especially
        when they don't have their own children to separate them)
      */
      let gcSiblings = _.zip(
        visibleGrandChildren.value(),
        visibleGrandChildren.rest().value()
        );
      gcSiblings.pop(); // removes the [last, undefined] pair at the end
      let cSiblings = _.zip(
        visibleChildren.value(),
        visibleChildren.rest().value()
        );
      cSiblings.pop();
      // also, the current node should not overlap its siblings
      let currentSiblings = [];
      if (self.curNode instanceof GoalNode && hasParent(self.curNode)) {
        let curNodeSiblings = _(self.curNode.parent.getViewChildren());
        currentSiblings = _.zip(
          curNodeSiblings.value(),
          curNodeSiblings.rest().value()
          );
        currentSiblings.pop();
      }
      let siblings = _(gcSiblings.concat(cSiblings, currentSiblings));
      let yFactors = siblings
        .map(function(e) {
        let a = e[0], b = e[1];
        let yDistance = nodeY(b) - nodeY(a);
        let wantedSpacing = ((a.height + b.height) / 2) + nodeVSpacing;
        return wantedSpacing / yDistance;
      })
        .value()
        ;
      self.yFactor = _.isEmpty(yFactors) ? self.height : _.max(yFactors);

      /*
        here we are looking for the descendant which should align with the current
        node. it used to be at the top of the view, now it's centered.
      */
      let centeredDescendant = undefined;
      if (self.curNode instanceof GoalNode) {
        let centeredTactic = self.curNode.getFocusedChild();
        if (centeredTactic !== undefined) {
          centeredDescendant = centeredTactic.getFocusedChild();
          if (centeredDescendant === undefined) {
            centeredDescendant = centeredTactic;
          }
        }
      } else if (self.curNode.isTacticish()) {
        alert("This should not happen!")
        let t = getTacticFromTacticish(self.curNode);
        if (t.goals.length > 0) {
          centeredDescendant = t.goals[t.goalIndex];
        }
      } else {
        throw self.curNode;
      }

      if (centeredDescendant !== undefined) {
        let curNode = self.curNode;
        if (curNode instanceof GoalNode
          && centeredDescendant instanceof GoalNode) {
          // computing the difference in height between the <hr> is not
          // obvious...
          let hrDelta =
            curNode.goalSpan[0].offsetTop
            - centeredDescendant.goalSpan[0].offsetTop
            ;
          self.descendantsOffset =
          self.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
          - (curGoal.height - centeredDescendant.height) / 2
          + hrDelta
          ;
        } else if (curNode.isTacticish()) {
          throw "This should not happen anymore?";
          /*
          let hrDelta =
            self.curNode.parent.goalSpan[0].offsetTop
            - centeredDescendant.goalSpan[0].offsetTop
            ;
          self.descendantsOffset =
          self.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
          - (curGoal.height - centeredDescendant.height) / 2
          + hrDelta
          ;
          */
        } else {
          self.descendantsOffset =
          self.yFactor * (nodeY(curGoal) - nodeY(centeredDescendant))
          ;
        }
      } else {
        self.descendantsOffset = 0;
      }

      // now we need to set the x and y attributes of the entering foreignObjects,
      // so we need to reuse the selection
      textEnter
        .attr("x", function(d) {
        if (hasParent(d)) {
          // non-roots are spawned at their parent's (cX0, cY0)
          d.cX0 = d.parent.cX0;
          d.cY0 = d.parent.cY0;
        } else {
          // the root needs to spawn somewhere arbitrary: (0, 0.5)
          d.cX0 = self.xOffset(d);
          d.cY0 = 0.5 * self.yFactor + self.yOffset(d);
        }
        return d.cX0;
      })
        .attr("y", function(d, ndx) { return d.cY0; })
      ;

      textSelection
        .each(function(d) {
        d.cX = nodeX(d) * self.xFactor + self.xOffset(d);
        d.cY = nodeY(d) * self.yFactor + self.yOffset(d);
      })
      // preset the width to update measures correctly
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .transition()
        .duration(animationDuration)
        .style("opacity", "1")
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
        .each("end", function() {
        // this is in "end" so that it does not trigger before nodes are positioned
        d3.select(this)
          .on("click", function(d) {

          //asyncLog("CLICK " + nodeString(d));

          d.click();

        })
        ;
      })
      ;

      textSelection.exit()
        .transition()
        .duration(animationDuration)
        .attr("x", function(d) {
        // in general, nodes should move towards the parent goal node
        if (!hasParent(d) || self.isRootNode(d)) {
          return d.cX;
        }
        if (d instanceof GoalNode) {
          let nodeToReach = d.parent.parent;
          d.cX = nodeToReach.cX;
          d.cY = nodeToReach.cY;
        } else {
          let nodeToReach = d.parent;
          d.cX = nodeToReach.cX;
          d.cY = nodeToReach.cY;
        }
        return d.cX;
      })
        .attr("y", function(d) { return d.cY; })
        .style("opacity", "0")
        .remove()
      ;

      let rectSelection = self.rectLayer.selectAll("rect").data(nodes, byNodeId);

      rectSelection.enter()
        .append("rect")
        .classed("goal", (d) => d instanceof GoalNode)
        .style("fill", function(d) {
        if (d instanceof GoalNode) { return "#AEC6CF"; }
        if (d.isTacticish()) { return "#CB99C9"; }
        return "#000000";
      })
        .classed("tactic", (d) => d.isTacticish())
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .attr("x", function(d) { return d.cX0; })
        .attr("y", function(d) { return d.cY0; })
        .attr("rx", function(d) { return d instanceof GoalNode ? 0 : 10; })
      ;

      rectSelection
        .classed("current", function(d) { return self.isCurNode(d); })
        .style("stroke", function(d) {
        return self.isCurNode(d) ? "#03C03C" : "";
      })
        .style("stroke-width", function(d) {
        return self.isCurNode(d) ? "4px" : "";
      })
        .classed("solved", function(d) { return d.solved; })
        .transition()
        .duration(animationDuration)
        .style("opacity", "1")
        .attr("width", function(d) { return d.width; })
        .attr("height", function(d) { return d.height; })
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
      ;

      rectSelection.exit()
        .transition()
        .duration(animationDuration)
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
        .style("opacity", "0")
        .remove()
      ;

      let linkSelection = self.linkLayer.selectAll("path").data(links, byLinkId);

      linkSelection.enter()
        .append("path")
        .classed("link", true)
        .attr("d",
        (d) => {
          let src = swapXY(centerRight0(d.source));
          let tgt = swapXY(centerLeft0(d.target));
          return self.diagonal({ "source": src, "target": tgt });
        })
        .attr("stroke",
        (d) => {
          let t = d.target;
          if (
            t instanceof TacticGroupNode
            && t.getFocusedTactic().goals.length === 0
            ) {
            return "#00FF00";
          } else {
            return "#000000";
          }
        })
      ;

      linkSelection
        .transition()
        .duration(animationDuration)
        .style("opacity", 1)
        .attr("d",
        (d) => {
          let src = swapXY(centerRight(d.source));
          let tgt = swapXY(centerLeft(d.target));
          return self.diagonal({ "source": src, "target": tgt });
        })
        .attr("stroke-width", self.linkWidth.bind(self))
      ;

      linkSelection.exit()
        .transition()
        .duration(animationDuration)
        .attr("d", function(d) {
        let src = swapXY(centerRight(d.source));
        let tgt = swapXY(centerLeft(d.target));
        return self.diagonal({ "source": src, "target": tgt });
      })
        .style("opacity", "0")
        .remove()
      ;

      let focusedGoal = self.getFocusedGoal();
      let diffData = (focusedGoal === undefined) ? [] : [focusedGoal];
      let diffSelection = self.diffLayer.selectAll("g.node-diff").data(
        diffData,
        byNodeId
        );

      diffSelection.enter()
        .append("g")
        .classed("node-diff", true)
        .classed("diff", true)
        .each(function(d) {
        // create these so that the field exists on first access
        d.addedSelections = [];
        d.removedSelections = [];
        // force the proper order of display, diffs on top of streams
        d.pathsGroup = d3.select(this).append("g").classed("paths", true); // streams
        d.rectsGroup = d3.select(this).append("g").classed("rects", true); // diffs
      })
        .style("opacity", 0)
        .transition()
        .duration(animationDuration)
        .style("opacity", 1)
      ;

      diffSelection
      // need to redo this every time now that nodes can change :(
        .each(function(d) {
        let gp = d.parent.parent;

        let d3this = d3.select(this);

        // adding diffs for the goal

        let subdiff = spotTheDifferences(gp.goalSpan, d.goalSpan);

        // there should be a goal stream whenever there are diffs
        let goalStreamData = subdiff.removed.length > 0 ? [undefined] : [];
        let goalStreamSelection =
          d.pathsGroup.selectAll("path.goalstream")
            .data(goalStreamData)
          ;

        goalStreamSelection.enter()
          .append("path")
          .classed("goalstream", true)
          .attr("fill", diffBlue)
          .attr("opacity", diffOpacity)
          .attr("stroke-width", 0)
          .attr(
          "d",
          connectRects(
            elmtRect0(gp, gp.goalSpan[0]),
            elmtRect0(d, d.goalSpan[0]),
            undefined //d.parent.cX + d.parent.width/2
            )
          )
        ;

        goalStreamSelection
          .transition()
          .duration(animationDuration)
          .attr(
          "d",
          connectRects(
            elmtRect(gp, gp.goalSpan[0]),
            elmtRect(d, d.goalSpan[0]),
            undefined //d.parent.cX + d.parent.width/2
            )
          )
        ;

        goalStreamSelection.exit()
          .remove()
        ;

        // let goalRemovedSelection =
        //     d.rectsGroup.selectAll("rect.goalremoved")
        //     .data(subdiff.removed)
        // ;

        // goalRemovedSelection.enter()
        //     .append("rect")
        //     .classed("goalremoved", true)
        //     .attr("fill", function(d, ndx) {
        //         return colorScale(ndx);
        //     })
        //     .attr("opacity", diffOpacity)
        // ;

        // goalRemovedSelection
        //     .each(function(jSpan) {
        //         let rect0 = elmtRect0(gp, jSpan[0]);
        //         let rect = elmtRect(gp, jSpan[0]);
        //         d3.select(this)
        //             .attr("width", rect.width)
        //             .attr("height", rect.height)
        //             .attr("x", rect0.left)
        //             .attr("y", rect0.top)
        //             .transition()
        //             .duration(animationDuration)
        //             .attr("x", rect.left)
        //             .attr("y", rect.top)
        //         ;
        //     })
        //         ;

        // let goalAddedSelection =
        //     d.rectsGroup.selectAll("rect.goaladded")
        //     .data(subdiff.added)
        // ;

        // goalAddedSelection.enter()
        //     .append("rect")
        //     .classed("goaladded", true)
        //     .attr("fill", function(d, ndx) {
        //         return colorScale(ndx);
        //     })
        //     .attr("opacity", diffOpacity)
        // ;

        // goalAddedSelection
        //     .each(function(jSpan) {
        //         let rect0 = elmtRect0(d, jSpan[0]);
        //         let rect = elmtRect(d, jSpan[0]);
        //         d3.select(this)
        //             .attr("width", rect.width)
        //             .attr("height", rect.height)
        //             .attr("x", rect0.left)
        //             .attr("y", rect0.top)
        //             .transition()
        //             .duration(animationDuration)
        //             .attr("x", rect.left)
        //             .attr("y", rect.top)
        //         ;
        //     })
        //         ;

        // adding diffs for the hypotheses
        let diffList = computeDiffList(gp.hyps, d.hyps);

        d.diffListSelection =
        d.pathsGroup.selectAll("g.diff-item")
          .data(diffList, byDiffId)
        ;

        d.diffListSelection.enter()
          .append("g")
          .classed("diff-item", true)
          .attr("id", byDiffId)
          .each(function(diff) {

          let d3this = d3.select(this);

          if (diff.oldHyp === undefined) {

            let newHyp = diff.newHyp;
            d3this
              .append("path")
              .attr("fill", diffGreen)
              .attr("opacity", diffOpacity)
              .attr("stroke-width", 0)
            ;

          } else if (diff.newHyp === undefined) {

            let oldHyp = diff.oldHyp;
            d3this
              .append("path")
              .attr("fill", diffRed)
              .attr("opacity", diffOpacity)
              .attr("stroke-width", 0)
            ;

          } else {

            let oldHyp = diff.oldHyp;
            let newHyp = diff.newHyp;
            if (JSON.stringify(oldHyp.hType)
              !== JSON.stringify(newHyp.hType)) {
              d3this
                .insert("path", ":first-child")
                .attr("fill", diffBlue)
                .attr("opacity", diffOpacity)
                .attr("stroke-width", 0)
              ;

            }

          }
        })
        ;

        // keep track of how far we are vertically to draw the diffs with
        // only one side nicely
        let leftY0 = gp.cY0 + goalBodyPadding;
        let rightY0 = d.cY0 + goalBodyPadding;
        let leftY = gp.cY + goalBodyPadding;
        let rightY = d.cY + goalBodyPadding;

        d.diffListSelection
          .each(function(diff) {

          if (diff.oldHyp === undefined) {
            let newHyp = diff.newHyp;
            d3.select(this).select("path")
              .attr(
              "d",
              connectRects(
                emptyRect0(gp, leftY0),
                elmtRect0(d, newHyp.div),
                undefined //d.parent.cX + d.parent.width/2
                )
              )
              .transition()
              .duration(animationDuration)
              .attr(
              "d",
              connectRects(
                emptyRect(gp, leftY),
                elmtRect(d, newHyp.div),
                undefined //d.parent.cX + d.parent.width/2
                )
              )
            ;
            rightY0 = elmtRect0(d, newHyp.div).bottom;
            rightY = elmtRect(d, newHyp.div).bottom;

          } else if (diff.newHyp === undefined) {

            let oldHyp = diff.oldHyp;
            d3.select(this).select("path")
              .attr(
              "d",
              connectRects(
                elmtRect0(gp, oldHyp.div),
                emptyRect0(d, rightY0),
                undefined //d.parent.cX + d.parent.width/2
                )
              )
              .transition()
              .duration(animationDuration)
              .attr(
              "d",
              connectRects(
                elmtRect(gp, oldHyp.div),
                emptyRect(d, rightY),
                undefined //d.parent.cX + d.parent.width/2
                )
              )
            ;
            leftY0 = elmtRect0(gp, oldHyp.div).bottom;
            leftY = elmtRect(gp, oldHyp.div).bottom;

          } else {

            let oldHyp = diff.oldHyp;
            let newHyp = diff.newHyp;
            if (JSON.stringify(oldHyp.hType) !== JSON.stringify(newHyp.hType)) {

              d3.select(this).select("path")
                .attr(
                "d",
                connectRects(
                  elmtRect0(gp, oldHyp.div),
                  elmtRect0(d, newHyp.div),
                  undefined //d.parent.cX + d.parent.width/2
                  )
                )
                .transition()
                .duration(animationDuration)
                .attr(
                "d",
                connectRects(
                  elmtRect(gp, oldHyp.div),
                  elmtRect(d, newHyp.div),
                  undefined //d.parent.cX + d.parent.width/2
                  )
                )
              ;

              let subdiff = spotTheDifferences(
                oldHyp.div,
                newHyp.div
                );

              // let diffId = byDiffId(diff);
              // d.removedSelections[diffId] =
              //     d.rectsGroup.selectAll("rect.removed")
              //     .data(subdiff.removed)
              // ;

              // d.removedSelections[diffId].enter()
              //     .append("rect")
              //     .classed("removed", true)
              //     .attr("fill", function(d, ndx) {
              //         return colorScale(ndx);
              //     })
              //     .attr("opacity", diffOpacity)
              // ;

              // d.removedSelections[diffId].exit()
              //     .remove()
              // ;

              // d.addedSelections[diffId] =
              //     d.rectsGroup.selectAll("rect.added")
              //     .data(subdiff.added)
              // ;

              // d.addedSelections[diffId].enter()
              //     .append("rect")
              //     .classed("added", true)
              //     .attr("fill", function(d, ndx) {
              //         return colorScale(ndx);
              //     })
              //     .attr("opacity", diffOpacity)
              // ;

              // d.addedSelections[diffId].exit()
              //     .remove()
              // ;

              // // TODO: there is a bug here where this does not get
              // // refreshed properly when nodes show up. To
              // // reproduce, load bigtheorem.v, run intros, and
              // // move down one tactic quickly.
              // //console.log(diff, byDiffId(diff));
              // let diffId = byDiffId(diff);

              // d.removedSelections[diffId]
              //     .each(function(jSpan) {
              //         let rect0 = elmtRect0(gp, jSpan[0]);
              //         let rect = elmtRect(gp, jSpan[0]);
              //         d3.select(this)
              //             .attr("width", rect.width)
              //             .attr("height", rect.height)
              //             .attr("x", rect0.left)
              //             .attr("y", rect0.top)
              //             .transition()
              //             .duration(animationDuration)
              //             .attr("x", rect.left)
              //             .attr("y", rect.top)
              //         ;
              //     })
              //         ;

              // d.addedSelections[diffId]
              //     .each(function(jSpan) {
              //         let rect0 = elmtRect0(d, jSpan[0]);
              //         let rect = elmtRect(d, jSpan[0]);
              //         d3.select(this)
              //             .attr("width", rect.width)
              //             .attr("height", rect.height)
              //             .attr("x", rect0.left)
              //             .attr("y", rect0.top)
              //             .transition()
              //             .duration(animationDuration)
              //             .attr("x", rect.left)
              //             .attr("y", rect.top)
              //         ;
              //     })
              //         ;

            }

            leftY0 = elmtRect0(gp, oldHyp.div).bottom;
            leftY = elmtRect(gp, oldHyp.div).bottom;

            /*
              we don't want to move the right cursor if the
              right hypothesis was not the very next
              hypothesis. this happens when a hypothesis gets
              moved down the list of hypotheses.
             */

            if (!diff.isJump) {
              rightY0 = elmtRect0(d, newHyp.div).bottom;
              rightY = elmtRect(d, newHyp.div).bottom;
            }

          }

        })
        ;

        d.diffListSelection.exit()
          .remove()
        ;

      });

      diffSelection.exit()
        .remove()
      ;

      // refocus the viewport

      self.viewportX = - (
        hasParent(curNode)
          ? curNode.parent.cX
          : curNode.cX // TODO: could do some math to align it the same way
        );

      self.viewportY =
      - (
        curNode instanceof GoalNode
          ? (curNode.cY + curNode.height / 2 - self.height / 2)
          : (curNode.parent.cY + curNode.parent.height / 2 - self.height / 2)
        )
      ;

      self.viewport
        .transition()
        .duration(animationDuration)
        .attr("transform",
        "translate(" + self.viewportX + ", " + self.viewportY + ")"
        )
      ;

      /*
        It is important to update cX0 for all nodes so that we can uniformly
        initialize links to start between their source's cX0 and their
        target's cX0.  Without this, links created from nodes that have moved
        away from their cX0 will seem to appear from the node's old position
        rather than its current one.
      */
      _(nodes).each(function(d) {
        d.x0 = d.x;
        d.y0 = d.y;
        d.cX0 = d.cX;
        d.cY0 = d.cY;
      });

      //this.updateDebug();

      onFulfilled();

    });

  }

  updateNodeMeasures(nodeDOM: Node, d: ProofTreeNode) {
    let elementToMeasure: HTMLElement =
      <HTMLElement>(
        d instanceof GoalNode
          ? nodeDOM // get the foreignObject itself
          : nodeDOM.firstChild // get the span
        );
    // we save in the rect field the size of the text rectangle
    let rect = elementToMeasure.getBoundingClientRect();
    d.width = d.nodeWidth();
    d.height = Math.ceil(rect.height);
  }

  xOffset(d: ProofTreeNode): number {
    return - d.nodeWidth() / 2; // position the center
  }

  yOffset(d: ProofTreeNode): number {
    let offset = - d.height / 2; // for the center
    let focusedChild = this.curNode.getFocusedChild();

    // all tactic nodes are shifted such that the current tactic is centered
    //assert(isGoal(this.curNode), "yOffset assumes the current node is a goal!");
    if (this.isCurGoalChild(d)) {
      assert(focusedChild !== undefined, "focusedChild === undefined");
      return offset + (nodeY(d.parent) - nodeY(focusedChild)) * this.yFactor;
    }

    // all goal grandchildren are shifted such that the context line of the
    // current goal and the current suboal align
    if (this.isCurGoalGrandChild(d)) {
      return offset + this.descendantsOffset;
    }

    // the other nodes (current goal and its ancestors) stay where they need
    return offset;
  }

}

function asyncStatus(): Promise<any> { throw "TODO"; }

let goalShare = 15 / 20;

function computeGoalWidth(width) {
  return Math.floor(width * (goalShare / 2));
}

let tacticShare = 4 / 20;

function computeTacticWidth(width) {
  return Math.floor(width * (tacticShare / 2));
}

function proofTreeQueryWish(s: string): void { throw "TODO"; }

/*
 * Returns a rect of the absolute position of [elmt] within the canvas. It needs
 * [node] in order to return absolute values, where [node] is the node element
 * within which [elmt] lives.
 */
function elmtRect(node, elmt) {
  let rect = elmt.getBoundingClientRect();
  let containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect();
  let left = node.cX + deltaX(containerRect, rect);
  let top = node.cY + deltaY(containerRect, rect);
  return {
    "left": left, "right": left + rect.width, "width": rect.width,
    "top": top, "bottom": top + rect.height, "height": rect.height,
  };
}

function elmtRect0(node, elmt) {
  let rect = elmt.getBoundingClientRect();
  let containerRect = $(elmt).parents("foreignObject")[0].getBoundingClientRect();
  let left = node.cX0 + deltaX(containerRect, rect);
  let top = node.cY0 + deltaY(containerRect, rect);
  return {
    "left": left, "right": left + rect.width, "width": rect.width,
    "top": top, "bottom": top + rect.height, "height": rect.height,
  };
}

type Rectangle = {
  bottom: number;
  left: number;
  right: number;
  top: number;
}

function deltaX(rect1: Rectangle, rect2: Rectangle): number {
  return rect2.left - rect1.left;
}
function deltaY(rect1: Rectangle, rect2: Rectangle): number {
  return rect2.top - rect1.top;
}

function makeGoalNodePre() {
  return $("<pre>")
    .addClass("goalNode")
  // inlining some CSS for svg_datatourl
    .css("font-family", "monospace")
    .css("font-size", "14px")
    .css("line-height", "normal")
    .css("margin", 0)
    .css("padding", 0)
    ;
}

function makeContextDivider() {
  return $("<hr>")
  // inlining the CSS for svg_datatourl
    .css("border", 0)
    .css("border-top", "1px solid black")
    .css("margin", 0)
    ;
}

function showBindersPar(t) {
  if (_.isEmpty(t)) { return ""; }
  return " (" + showBinder(t[0]) + ")" + showBindersPar(_(t).rest().value());
}

function showBinders(t) {
  if (_.isEmpty(t)) { return ""; }
  if (t.length === 1) { return ' ' + showBinder(t[0]); }
  return " (" + showBinder(t[0]) + ")" + showBindersPar(_(t).rest().value());
}

function showBinder(t) {
  if (t[1] === null) {
    return showNames(t[0]);
  } else {
    return showNames(t[0]) + syntax(":") + ' ' + showTermAux(t[1], 0, 0, false);
  }
}

function showPatternAux(p, withParens) {
  let c = p.contents;
  switch (p.tag) {
    case "Wildcard":
      return "_";

    case "Pattern":
      if (c[1].length === 0) { // constructor with no parameters, never parenthesized
        return c[0];
      } else { // constructor with parameters, parenthesized if subpattern
        if (c[0] === "cons" && c[1].length === 2) {
          return (withParens ? syntax("(") : "")
            + showPatternAux(c[1][0], true)
            + ' ' + syntax("::") + ' '
            + showPattern(c[1][1])
            + (withParens ? syntax(")") : "")
            ;
        } else {
          return (withParens ? syntax("(") : "")
            + _(c[1]).reduce(function(acc, elt) {
              return acc + " " + showPatternAux(elt, true);
            }, c[0])
            + (withParens ? syntax(")") : "")
            ;
        }
      }

    case "OrPatterns":
      let patterns = c[0];
      return (
        syntax("(")
        + _(patterns).reduce(function(acc, orpattern, ndx) {
          return (
            (ndx > 0 ? syntax(",") : "")
            + _(orpattern).reduce(function(acc, pattern, ndx) {
              return (
                (ndx > 0 ? "|" : "")
                + showPatternAux(pattern, false)
                );
            })
            );
        })
        + syntax(")")
        );

    default:
      alert("Unknown pattern: " + p.tag);

  };
}

function showPattern(p) { return showPatternAux(p, false); }

function showPatterns(ps) {
  if (ps.length === 1) {
    let patterns = ps[0];
    return _(patterns).rest().reduce(function(acc, pattern) {
      return acc + syntax(", ") + showPattern(pattern);
    }, showPattern(patterns[0]));
  } else {
    alert("TODO");
  }
}

function showName(t) {
  if (t === null) { // underscore
    return ident('_');
  } else {
    return ident(t);
  }
}

function showNames(t) {
  if (_.isEmpty(t)) { return ""; }

  return showName(t[0]) + " " + showNames(_(t).rest().value());
}

function showTerm(t) {
  let term = mkTerm(t);
  console.log(term, term.toString());
  return showTermAux(t, 0, 0, true);
}

function showTermIndent(t, indent) {
  return showTermAux(t, indent, 0, true);
}

function getIndent(depth) {
  return repeat(2 * depth, " ");
}

function extractGoal(gGoal) {

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

function extractHypothesis(gHyp) {

  if (gHyp.hasOwnProperty("Left")) {
    // this tries to approximate parsing...
    let matches = gHyp.Left.match(/^([\s\S]*) := ([\s\S]*) : ([\s\S]*)$/);
    if (matches !== null) {
      gHyp = {
        "hName": matches[1],
        "hValue": { "contents": matches[2], "tag": "Raw" },
        "hType": { "contents": matches[3], "tag": "Raw" },
      };
    } else {
      matches = gHyp.Left.match(/^([\s\S]*) : ([\s\S]*)$/);
      gHyp = {
        "hName": matches[1],
        "hValue": null,
        "hType": { "contents": matches[2], "tag": "Raw" },
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

function vernac(s) { return '<span class="vernac">' + s + '</span>'; }
function syntax(s) { return '<span class="syntax">' + s + '</span>'; }
function ident(s) { return '<span class="identifier">' + s + '</span>'; }
function term(s) { return '<span class="term">' + s + '</span>'; }

function showConstructor(t) {
  let name = t[0];
  if (t[1] === null) {
    return syntax("|")
      + ' '
      + ident(name)
      ;
  } else {
    let type = showTermInline(t[1]);
    return syntax("|")
      + ' '
      + ident(name)
      + ' '
      + syntax(":")
      + ' '
      + type
      ;
  }
}

function showVernac(t) {
  let c = t.contents;
  let args, name, term, type;

  switch (t.tag) {

    case "Inductive":
      name = c[0];
      type = showTermInline(c[1]);
      let constructors = _(c[2]).map(showConstructor);
      return vernac("Inductive")
        + ' '
        + ident(name)
        + ' '
        + syntax(":")
        + ' '
        + type
        + ' '
        + syntax(":=")
        + "<br>"
        + _(constructors).reduce(function(acc, elt) { return acc + elt + "<br>"; }, "")
        + syntax(".")
        ;

    case "Theorem":
      name = c[0];
      type = showTermInline(c[1]);
      return vernac("Theorem")
        + ' '
        + ident(name)
        + ' '
        + syntax(":")
        + ' '
        + type
        + syntax(".")
        ;

    case "Definition":
      name = c[0];
      args = _(c[1]).map(showBinder);
      type = (c[2] !== null)
        ? syntax(":") + ' ' + showTermInline(c[2]) + ' '
        : "";
      term = showTermIndent(c[3], 1);
      return vernac("Definition")
        + ' '
        + ident(name)
        + ' '
        + _(args).reduce(function(acc, elt) {
          return acc + syntax("(") + elt + syntax(")") + ' ';
        }, "")
        + type
        + syntax(":=")
        + "<br>" + getIndent(1)
        + term
        + syntax(".")
        ;

    case "Fixpoint":
      name = c[0];
      args = _(c[1]).map(showBinder);
      let decreasing = c[2];
      type = (c[3] !== null)
        ? syntax(":") + ' ' + showTermInline(c[3]) + ' '
        : "";
      term = showTermIndent(c[4], 1);
      return vernac("Fixpoint")
        + ' '
        + ident(name)
        + ' '
        + _(args).reduce(function(acc, elt) {
          return acc + syntax("(") + elt + syntax(")") + ' ';
        }, "")
        + (
          (decreasing !== null)
            ? syntax("{") + ' ' + syntax("struct")
            + ' ' + decreasing + ' ' + syntax("}") + ' '
            : ""
          )
        + type
        + syntax(":=")
        + "<br>" + getIndent(1)
        + term
        + syntax(".")
        ;

    default:
      return "Unknown Vernacular tag: " + t.tag;

  };
}

function showTermText(t) {
  return $(showTermInline(t)).text();
}

function showMatchItems(items) {
  return _(items).reduce(function(acc, item, ndx) {
    let term = item[0];
    let matchAs = item[1];
    let matchIn = item[2];
    return (
      acc
      + (ndx > 0 ? syntax(",") + ' ' : "")
      + showTermInline(term)
      + (matchAs ? ' ' + syntax("as") + ' ' + matchAs : "")
      + (matchIn ? ' ' + syntax("in") + ' ' + showTermInline(matchIn) : "")
      );
  }, "");
}

/*
  [t]           the term to show
  [indentation] the indentation to use if you make a newline
  [precParent]  the precedence of the parent operator (for parenthesizing)
  [newline]     true if the term should feel free to use multiple lines
*/
function showTermAux(t, indentation, precParent, newline) {
  let c = t.contents;

  let indent = getIndent(indentation);

  let par = function(precOp, text) {
    if (precOp <= precParent) {
      return term(syntax("(") + text + syntax(")"));
    } else {
      return term(text);
    }
  };

  let showOp = function(c, op, precOp) {
    return par(
      precOp,
      showTermAux(c[0].contents[1], 0, precOp, false)
      + " " + syntax(op) + " "
      + showTermAux(c[1], 0, precOp, false)
      );
  };

  switch (t.tag) {

    case "Raw":
      return '<span>' + c + '</span>';

    case "Var":
      if (t.type !== undefined) {
        return '<span style="font-weight: bold;"'
          + ' title="' + t.type + '">'
          + c + '</span>'
          ;
      } else {
        return term(c);
      }

    case "Forall":
      return par(
        precForall,
        syntax("forall") + showBinders(c[0]) + syntax(",")
        + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
        + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Lambda":
      return par(
        precMin,
        syntax("fun") + showBinders(c[0]) + ' ' + syntax("=>")
        + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
        + showTermAux(c[1], indentation + 1, precMin, newline)
        );

    case "Exists":
      return par(
        precForall,
        syntax("exists") + showBinders(c[0]) + syntax(",")
        + (newline ? "<br/>" + getIndent(indentation + 1) : " ")
        + showTermAux(c[1], indentation + 1, precParent, newline)
        );

    case "Arrow":
      return term(
        showTermAux(c[0], indentation, precArrow, false)
        + ' ' + syntax("->")
        + (newline ? "<br/>" + indent : " ")
        + showTermAux(c[1], indentation, precParent, newline)
        );

    case "Match":
      let matchItems = c[0];
      let maybeType = c[1];
      let equations = c[2];
      return term(
        syntax("match") + ' '
        + showMatchItems(matchItems) + ' '
        + (maybeType
          ? syntax(":") + ' ' + showTermAux(c[1], 0, precMin, false)
          : ""
          )
        + syntax("with") + "<br>"
        + _(equations).reduce(function(acc, elt) {
          let patterns = showPatterns(elt[0]);
          let body = showTermAux(elt[1], indentation + 1, precParent, newline);
          return acc
            + getIndent(indentation) + syntax("|") + ' '
            + patterns
            + ' '
            + syntax("=>")
            + (
              (body.indexOf("<br>") === -1)
                ? ' ' + body
                : "<br>" + getIndent(indentation + 1) + body
              )
            + "<br>";
        }, "")
        //showTermAux(c[0], indentation, precArrow, false)
        + getIndent(indentation) + syntax("end")
        );

    case "App":

      // handling special case of infix operators I want to pretty print
      if (c[0].contents === "not"
        && c[1].contents[0].contents[0].contents === "eq"
        ) {
        return par(
          precNotEqual,
          showTermAux(c[1].contents[0].contents[1], 0, precNotEqual, false)
          + " ≠ "
          + showTermAux(c[1].contents[1], 0, precNotEqual, false)
          )
      }

      if (c[0].tag === "App") {
        switch (c[0].contents[0].contents) {

          case "eq":
            return showOp(c, "=", precEqual);

          case "plus":
            return showOp(c, "+", precPlus);

          case "minus":
            return showOp(c, "-", precMinus);

          case "mult":
            return showOp(c, "*", precMult);

          case "and":
            return showOp(c, "/\\", precAnd);

          case "or":
            return showOp(c, "\\/", precOr);

          case "andb":
            return showOp(c, "&&", precAndB);

          case "orb":
            return showOp(c, "||", precOrB);

          case "iff":
            return showOp(c, "<->", precEquiv);

          // case "cons":
          //     return showOp(c, "::", precCons);

          // case "app":
          //     return showOp(c, "++", precAppend);

          default:
          // nothing, fall through

        };
      }

      return par(
        precApp,
        showTermAux(c[0], 0, precApp - 1, false) + " "
        + showTermAux(c[1], 0, precApp, false)
        );

    default:
      return "Unknown tag " + t.tag;

  };
}

function inlineBlock(contents) {
  return '<div style="display: inline-block; max-width: 100%; vertical-align: top;">' + contents + '</div>';
}

function showHypothesis(h) {
  let res = h.hName;
  if (h.hValue !== null) {
    res = res + ' ' + syntax(":=") + ' ' + showTermInline(h.hValue);
  }
  res = inlineBlock(res + ' ' + syntax(":") + ' ')
  + inlineBlock(showTermInline(h.hType));
  return res;
}

function showHypothesisText(h) {
  let res = h.hName;
  if (h.hValue !== null) {
    res = res + " := " + showTermText(h.hValue);
  }
  res = res + " : " + showTermText(h.hType);
  return res;
}

function showTermInline(t) {
  return showTermAux(t, 0, 0, false);
}

function getResponseFocused(response) {
  return response.rGoals.focused;
}

function getResponseUnfocused(response) {
  return response.rGoals.unfocused;
}

function hasParent(n) {
  return n.parent !== undefined;
}

function hasGrandParent(n) {
  return hasParent(n) && hasParent(n.parent);
}

function byNodeId(d) { return d.id; }
function byLinkId(d) { return d.source.id + "," + d.target.id; }

// transposition accessors
function nodeX(d) { return d.y; }
function nodeY(d) { return d.x; }

function getClosestGoal(node: ProofTreeNode): GoalNode {
  if (node instanceof GoalNode) { return node; }
  // if it is not a goal, it ought to have a parent
  if (node instanceof TacticGroupNode) {
    return <GoalNode>node.parent;
  }
  if (node instanceof TacticNode) {
    let parent = node.parent;
    if (parent instanceof GoalNode) {
      alert("This should not happen anymore!");
      // TODO: remove this if it indeed does not happen
      return parent;
    } else if (parent instanceof TacticGroupNode) {
      return <GoalNode>parent.parent;
    }
  }
  throw node;
}

function getTacticFromTacticish(d: ProofTreeNode): TacticNode {
  if (d instanceof TacticNode) {
    return d;
  } else if (d instanceof TacticGroupNode) {
    return d.getFocusedTactic();
  } else {
    throw d;
  }
}

// specialized version of console.log, because JS is stupid
function outputError(error: any): void {
  console.log(error, error.stack);
}

function goalNodeUnicityRepr(node: GoalNode): string {
  return JSON.stringify({
    "goalTerm": node.goalTerm,
    "hyps": _(node.hyps)
      .map(function(h) {
      return {
        "hName": h.hName,
        "hValue": h.hValue,
        "hType": h.hType,
      };
    })
      .value(),
  });
}

function tacticNodeUnicityRepr(node: TacticNode): string {
  return JSON.stringify(
    _(node.goals)
      .map(goalNodeUnicityRepr)
      .value()
    );
}

function asyncQueryAndUndo(t: string): Promise<any> {
  throw "TODO";
}

function isGood(response: any) { throw "TODO"; }

let centerLeftOffset = +10;

let centerRightOffset = -10;

function centerLeft0(d) {
  return {
    "x": d.cX0 + centerLeftOffset,
    "y": d.cY0 + d.height / 2
  };
}

function centerRight0(d) {
  return {
    "x": d.cX0 + d.width + centerRightOffset,
    "y": d.cY0 + d.height / 2
  };
}

function centerLeft(d) {
  return {
    "x": d.cX + centerLeftOffset,
    "y": d.cY + d.height / 2
  };
}

function centerRight(d) {
  return {
    "x": d.cX + d.width + centerRightOffset,
    "y": d.cY + d.height / 2
  };
}

/*
  This might be terrible design, but [spotTheDifference] currently marks inline
  diffs through CSS background-color. It's much more stable than using
  rectangles when animated.
 */
function spotTheDifferences(before, after) {

  function rec(before, after) {

    let nbBefore = before.children().length;
    let nbAfter = after.children().length;
    if (nbBefore !== nbAfter) {
      return [{
        "removed": before,
        "added": after,
      }];
    }

    let nbChildren = nbBefore;
    if (nbChildren === 0) { // both leaves
      if (before.html() !== after.html()) {
        return [{
          "removed": before,
          "added": after,
        }];
      } else {
        return [];;
      }
    }

    let everyChildChanged = true;

    let childrenChanges = _.range(nbChildren).reduce(function(acc, i) {
      let tmp = rec($(before.children()[i]), $(after.children()[i]));
      if (tmp.length === 0) { everyChildChanged = false; }
      return acc.concat(tmp);
    }, [])
      ;

    if (everyChildChanged) {
      return [{
        "removed": before,
        "added": after,
      }];
    } else {
      return childrenChanges;
    }

  }

  let removed = [];
  let added = [];

  _(rec($(before).children(), $(after).children())).each(function(pair, ndx) {
    pair.removed.css("background-color", diffColor(ndx));
    pair.added.css("background-color", diffColor(ndx));
    //removed.push(pair.removed);
    //added.push(pair.added);
  });

  return { "removed": removed, "added": added };
}

function avg(n1, n2) { return (n1 + n2) / 2; }

function mkDot(x, y) { return { "x": x, "y": y }; }

function showDot(d) { return d.x + " " + d.y; }

/*

  a_____b     c_____d
  |     |     |     |
  h_____g     f_____e

*/
function connectRects(r1, r2, rightsLeft) {
  //console.log("rect1", r1, "rect2", r2);
  if (rightsLeft === undefined) { rightsLeft = r2.left; }
  let a = mkDot(r1.left, r1.top);
  let b = mkDot(r1.right, r1.top);
  let c = mkDot(rightsLeft, r2.top);
  let d = mkDot(r2.right, r2.top);
  let e = mkDot(r2.right, r2.bottom);
  let f = mkDot(rightsLeft, r2.bottom);
  let g = mkDot(r1.right, r1.bottom);
  let h = mkDot(r1.left, r1.bottom);

  let cp1 = mkDot(avg(b.x, c.x), b.y);
  let cp2 = mkDot(avg(f.x, g.x), c.y);
  let cp3 = mkDot(avg(f.x, g.x), f.y);
  let cp4 = mkDot(avg(f.x, g.x), g.y);

  //console.log("M", a, b, c, d, e, f, g, h);

  return (
    "M" + showDot(a)
    + "L" + showDot(b)
    + "C" + showDot(cp1) + "," + showDot(cp2) + "," + showDot(c)
    + "L" + showDot(d) + "," + showDot(e) + "," + showDot(f)
    + "C" + showDot(cp3) + "," + showDot(cp4) + "," + showDot(g)
    + "L" + showDot(h)
    + "Z"
    );
}

function byDiffId(d) {
  let res = "{";
  if (d.oldHyp !== undefined) { res += d.oldHyp.hName; }
  res += "-";
  if (d.newHyp !== undefined) { res += d.newHyp.hName; }
  return res + "}";
}

function sameNameAs(a) {
  return function(b) { return a.hName === b.hName; };
}

function computeDiffList(oldHypsOriginal, newHypsOriginal) {
  let diffList = [];

  // slice() creates a shallow copy, since we will mutate this
  let oldHyps = oldHypsOriginal.slice();
  let newHyps = newHypsOriginal.slice();

  while (oldHyps.length > 0 && newHyps.length > 0) {
    let oldHyp = oldHyps[0];
    let newHyp = newHyps[0];
    // either the first two match
    if (oldHyp.hName === newHyp.hName) {
      diffList.push({ "oldHyp": oldHyp, "newHyp": newHyp, "isJump": false });
      oldHyps.shift();
      newHyps.shift();
      continue;
    }
    let matchesOld = _(newHyps).find(sameNameAs(oldHyp));
    // or the first old has disappeared
    if (matchesOld === undefined) {
      diffList.push({ "oldHyp": oldHyp, "newHyp": undefined, "isJump": false });
      oldHyps.shift();
      continue;
    }
    // or the first old has moved, but the first new has appeared
    let matchesNew = _(oldHyps).find(sameNameAs(newHyp));
    if (matchesNew === undefined) {
      diffList.push({ "oldHyp": undefined, "newHyp": newHyp, "isJump": false });
      newHyps.shift();
      continue;
    }
    // otherwise, register matchesOld as a "jump"
    diffList.push({ "oldHyp": oldHyp, "newHyp": matchesOld, "isJump": true });
    oldHyps.shift();
    _(newHyps).remove(sameNameAs(matchesOld));
  }

  // now register the remaining disappearing
  _(oldHyps).each(function(oldHyp) {
    diffList.push({ "oldHyp": oldHyp, "newHyp": undefined, "isJump": false });
  });

  // now register the remaining appearing
  _(newHyps).each(function(newHyp) {
    diffList.push({ "oldHyp": undefined, "newHyp": newHyp, "isJump": false });
  });

  return diffList;
}

/*
  creates an empty rectangle in the same column as [node], at vertical position
  [currentY]
*/
function emptyRect(node: ProofTreeNode, currentY: number): Rectangle {
  let delta = 1; // how big to make the empty rectangle
  return $.extend(
    {
      "left": node.cX,
      "right": node.cX + node.width,
      "width": node.width
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
    );
}

function emptyRect0(node: ProofTreeNode, currentY: number): Rectangle {
  let delta = 1; // how big to make the empty rectangle
  return $.extend(
    {
      "left": node.cX0,
      "right": node.cX0 + node.width,
      "width": node.width
    },
    {
      "top": currentY - delta,
      "bottom": currentY + delta,
      "height": 2 * delta,
    }
    );
}

function repeat(n: number, s: string): string {
  return Array(n + 1).join(s);
}

let diffColor = (function() {
    let colors = [
        "#ffbb78",
        "#f7b6d2",
        "#dbdb8d",
        "#6b6ecf",
        "#8ca252",
        "#b5cf6b",
        "#cedb9c",
        "#bd9e39",
        "#d6616b",
        "#ce6dbd",
        "#de9ed6",
    ];
    let scale = d3.scale.ordinal().range(colors);
    return function(n) {
        return scale(n);
    };
})();
