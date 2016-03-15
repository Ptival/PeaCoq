/* Globals to be configured */
let animationDuration = 2000;
// let diffBlue = "#8888EE";
// let diffGreen = "#88EE88";
// let diffOrange = "#FFB347";
// let diffOpacity = 0.75;
// let diffRed = "#EE8888";
let goalBodyPadding = 4;
let verticalSpacingBetweenNodes = 10;

/* Globals not to be touched */

/* 0 is the active tree, rest is stack of background ones*/
let proofTrees: ProofTree[] = [];

class ProofTree {
  anchor: d3.Selection<HTMLElement>;
  /* whatever the client wants to store as meta-data */
  clientState: Object;
  private _curNode: GoalNode;
  descendantsOffset: number;
  //diagonal: d3.svg.Diagonal<ProofTreeLink, ProofTreeNode>;
  height: number;
  name: string;
  paused: boolean;
  /* true until the user uses their mouse */
  usingKeyboard: boolean;
  rootNode: GoalNode;
  //stateId: number;
  svgId: string;
  tactics: () => TacticGroup[];
  tacticsWorklist: WorklistItem[];
  tacticWaiting: Maybe<string>;
  //tacticWaitingForContext: Maybe<TacticWaiting>;
  tree: d3.layout.Tree<ProofTreeNode>;
  viewportX: number;
  viewportY: number;
  private width: number;
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
    anchor: HTMLElement,
    width: number,
    height: number
  ) {
    let self = this;

    width = Math.max(0, width);
    height = Math.max(0, height);

    this.name = name;
    this.anchor = d3.select(anchor);
    this.width = width;
    this.height = height;

    this.paused = false;
    this.svgId = _.uniqueId();
    this.xFactor = this.width;
    this.yFactor = this.height;
    this.clientState = {};
    this.usingKeyboard = true; // true until the user moves their mouse
    this.tacticWaiting = nothing();

    this.tree = d3.layout.tree<ProofTreeNode>()
      .children((node: ProofTreeNode, index: number) => {
        // fake nodes are used to trick the layout engine into spacing
        // childrenless nodes appropriately
        if (node instanceof FakeNode) { return []; }
        let viewChildren = node.getViewChildren();
        if (viewChildren === undefined) { throw ["children", node]; }
        // in order to trick d3 into displaying tactics better add fake
        // children to tactic nodes that solve their goal
        if (node instanceof TacticGroupNode && viewChildren.length === 0) {
          return [new FakeNode(self, node)];
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
        "translate(" + self.getGoalWidth() + ", 0)"
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

    // if (svgPanEnabled) {
    //   this.svg.insert("script", ":first-child").attr("xlink:href", "SVGPan.js");
    // }

  }

  /*
    here we are looking for the descendant which should align with the current
    node. it used to be at the top of the view, now it's centered.
  */
  computeDescendantsOffset() {

    let self = this;
    let curNode = this.curNode;

    let centeredDescendant =
      this.curNode.getFocusedChild().caseOf<Maybe<ProofTreeNode>>({
        nothing: () => nothing(),
        just: (fc) => fc.getFocusedChild().caseOf({
          nothing: () => just(fc),
          just: (fgc) => just(fgc),
        })
      });

    centeredDescendant.caseOf({
      nothing: () => { self.descendantsOffset = 0; },
      just: (d) => {
        if (d instanceof GoalNode) {
          // computing the difference in height between the <hr> is not
          // obvious...
          let hrDelta = curNode.html[0].offsetTop - d.html[0].offsetTop;
          this.descendantsOffset = (
            this.yFactor * (nodeY(curNode) - nodeY(d))
            - (curNode.getHeight() - d.getHeight()) / 2
            + hrDelta
          );
        } else {
          this.descendantsOffset =
            this.yFactor * (nodeY(curNode) - nodeY(d))
            ;
        }
      }
    });

  }

  computeXYFactors() {
    let curGoal = this.curNode;
    let visibleChildren = _(curGoal.getViewChildren());
    let visibleGrandChildren = _(curGoal.getViewGrandChildren());
    let emptyNodeArray: ProofTreeNode[] = [];
    let visibleNodes = _(emptyNodeArray);
    curGoal.getParent().fmap((p) => {
      visibleNodes = visibleNodes.concat([p]);
    });
    visibleNodes = visibleNodes.concat([curGoal]);
    visibleNodes = visibleNodes.concat(visibleChildren.value());
    visibleNodes = visibleNodes.concat(visibleGrandChildren.value());

    // xFactor is now fixed, so that the user experience is more stable
    let rootViewChildren = this.rootNode.getViewChildren();
    if (rootViewChildren.length === 0) {
      this.xFactor = this.width;
    } else {
      let xDistance = nodeX(rootViewChildren[0]) - nodeX(this.rootNode);
      /* width = 4 * xDistance * xFactor */
      this.xFactor = this.width / (4 * xDistance);
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
      visibleGrandChildren.tail().value()
    );
    gcSiblings.pop(); // removes the [last, undefined] pair at the end
    let cSiblings = _.zip(
      visibleChildren.value(),
      visibleChildren.tail().value()
    );
    cSiblings.pop();
    // also, the current node should not overlap its siblings
    let currentSiblings = [];
    if (this.curNode instanceof GoalNode && this.curNode.hasParent()) {
      let curNodeSiblings = _(fromJust(this.curNode.getParent()).getViewChildren());
      currentSiblings = _.zip(
        curNodeSiblings.value(),
        curNodeSiblings.tail().value()
      );
      currentSiblings.pop();
    }
    let siblings = _(gcSiblings.concat(cSiblings, currentSiblings));
    let yFactors = siblings
      .map(function(e) {
        let a = e[0], b = e[1];
        let yDistance = nodeY(b) - nodeY(a);
        let wantedSpacing = ((a.getHeight() + b.getHeight()) / 2) + verticalSpacingBetweenNodes;
        return wantedSpacing / yDistance;
      })
      .value()
      ;
    this.yFactor = _.isEmpty(yFactors) ? this.height : _.max(yFactors);
  }

  get curNode(): GoalNode { return this._curNode; }
  set curNode(n: GoalNode) { this._curNode = n; }

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

  getAllNodes(): ProofTreeNode[] { return this.rootNode.getAllDescendants(); }

  getCurrentGoal(): GoalNode {
    assert(this.curNode instanceof GoalNode, "getCurrentGoal: curNode instanceof GoalNode");
    return this.curNode;
  }

  getFocus() { $(":focus").blur(); }

  getGoalWidth() {
    let goalShare = 15 / 20;
    return Math.floor(this.width * (goalShare / 2));
  }

  getTacticWidth() {
    let tacticShare = 4 / 20;
    return Math.floor(this.width * (tacticShare / 2));
  }

  getCurrentScale() {
    return (<any>this.svg[0][0]).currentScale;
  }

  /*
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
  */

  isCurGoal(n: ProofTreeNode): boolean {
    return n.id === this.curNode.id;
  }

  isCurGoalChild(n: ProofTreeNode): boolean {
    let self = this;
    return n.hasParentSuchThat((p) => self.isCurGoal(p));
  }

  isCurGoalGrandChild(n: ProofTreeNode): boolean {
    let self = this;
    return n.hasParentSuchThat((p) => self.isCurGoalChild(p));
  }

  isCurNode(n: ProofTreeNode): boolean { return n.id === this.curNode.id; }

  isCurNodeAncestor(strictly: Strictly, n: ProofTreeNode): boolean {
    let common = commonAncestor(n, this.curNode);
    let commonAncestorIsNode = common.id === n.id;
    switch (strictly) {
      case Strictly.Yes: return commonAncestorIsNode && !this.isCurNode(n);
      case Strictly.No: return commonAncestorIsNode;
    };
  }

  isCurNodeChild(n: ProofTreeNode): boolean {
    let self = this;
    return n.hasParentSuchThat((p) => self.isCurNode(p));
  }

  isCurNodeDescendant(strictly: Strictly, n: ProofTreeNode): boolean {
    let common = commonAncestor(n, this.curNode);
    let commonAncestorIsCurNode = common.id === this.curNode.id;
    switch (strictly) {
      case Strictly.Yes: return commonAncestorIsCurNode && !this.isCurNode(n);
      case Strictly.No: return commonAncestorIsCurNode;
    };
  }

  isCurNodeGrandChild(n: ProofTreeNode): boolean {
    let self = this;
    return n.hasParentSuchThat((p) => self.isCurNodeChild(p));
  }

  isCurNodeParent(n: ProofTreeNode): boolean {
    let self = this;
    return this.curNode.hasParentSuchThat((p) => p.id === n.id);
  }

  // isCurNodeSibling(n: ProofTreeNode): boolean {
  //   return !this.isCurNode(n) && hasParent(n) && this.isCurNodeParent(n.getParent());
  // }

  isRootNode(n: ProofTreeNode): boolean {
    return n.id === this.rootNode.id;
  }

  keydownHandler() {

    let ev: any = d3.event;

    // don't interact while typing
    if (ev.target.type === "textarea") { return; }

    var curNode = this.curNode;

    var children = curNode.getViewChildren();

    this.usingKeyboard = true;

    //console.log(d3.event.keyCode);

    switch (ev.keyCode) {

      case 37: // Left
        //case 65: // a
        ev.preventDefault();
        if (curNode.hasParent()) {
          //asyncLog("LEFT " + nodeString(curNode.parent));
          fromJust(curNode.getParent()).click();
        } else {
          // when at the root node, undo the last action (usually Proof.)
          //onCtrlUp(false);
        }
        break;

      case 39: // Right
        //case 68: // d
        ev.preventDefault();
        curNode.getFocusedChild().fmap((dest) => {
          //asyncLog("RIGHT " + nodeString(dest));
          dest.click()
        });
        break;

      case 38: // Up
        //case 87: // w
        ev.preventDefault();
        if (ev.shiftKey) {
          //this.shiftPrevGoal(curNode.getFocusedChild());
        } else {
          this.shiftPrevByTacticGroup(curNode);
        }
        break;

      case 40: // Down
        //case 83: // s
        ev.preventDefault();
        if (ev.shiftKey) {
          //this.shiftNextGoal(curNode.getFocusedChild());
        } else {
          this.shiftNextByTacticGroup(curNode);
        }
        break;

      case 219: // [
        var focusedChild = curNode.getFocusedChild();
        focusedChild.fmap((c) => (<TacticGroupNode>c).shiftPrevInGroup());
        break;

      case 221: // ]
        var focusedChild = curNode.getFocusedChild();
        focusedChild.fmap((c) => (<TacticGroupNode>c).shiftNextInGroup());
        break;

      default:
        //console.log("Unhandled event", d3.event.keyCode);
        return;
    }

    // EDIT: now that we integrate the proof tree, it's best to let stuff bubble up
    // if we haven't returned, we don't want the normal key behavior
    //d3.event.preventDefault();

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

    let curNode = this.curNode;

    // if the user uses his keyboard, highlight the focused path
    // if (curNode instanceof GoalNode) {

    return this.curNode.getFocusedChild().caseOf({
      nothing: () => thin,
      just: (focusedChild) => {
        if (this.isCurNode(src) && focusedChild.id === tgt.id) { return thick; }
        return focusedChild.getFocusedChild().caseOf({
          nothing: () => thin,
          just: (focusedGrandChild) => {
            return (
              focusedChild.id == src.id && focusedGrandChild.id === tgt.id
                ? thick : thin
            );
          },
        });
      },
    });

    //
    // } else if (curNode instanceof TacticGroupNode) {
    //   let focusedChild = this.curNode.getFocusedChild();
    //   if (focusedChild !== undefined && tgt.id === focusedChild.id) {
    //     return thick;
    //   }
    //   return thin;
    // } else {
    //   throw this.curNode;
    // }

  }

  onRectSelectionEnter(s: d3.selection.Enter<ProofTreeNode>): void {
    s
      .append("rect")
      .classed("goal", (d) => d instanceof GoalNode)
      .classed("tactic", (d) => d instanceof TacticGroupNode)
      .attr("width", function(d) { return d.getWidth(); })
      .attr("height", function(d) { return d.getHeight(); })
      .attr("x", (d) => d.getOriginalScaledX())
      .attr("y", (d) => d.getOriginalScaledY())
      .attr("rx", function(d) { return d instanceof GoalNode ? 0 : 10; })
      ;
  }

  processTactics(): Promise<any> {

    /*
      every time curNode is changed, the tacticsWorklist should be
      flushed, so that [runTactic] can reliably add the results of running
      the tactic to the current node
    */

    if (_(this.tacticsWorklist).isEmpty()) {
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

    return;
    //
    // //if (focusedOnEditor) { return; }
    //
    // let self = this;
    // let curNode = this.curNode;
    //
    // let tacticsAndGroups = this.tactics();
    //
    // /*
    //   _(this.tactics())
    //     .groupBy(function(elt) {
    //     if ($.type(elt) === "string") {
    //       return "tactics";
    //     } else {
    //       return "groups";
    //     }
    //   })
    //     .value()
    //   ;
    //
    //   // TODO: there should be no tactics!
    //   let groups = tacticsAndGroups.groups;
    //   */
    //
    // /*
    //     let groupSparks = _(tacticsAndGroups)
    //       .map(function(group) {
    //       let groupNode: TacticGroupNode = self.findOrCreateGroup(curNode, group.name);
    //       return (
    //         _(group.tactics)
    //           .filter(
    //           (tactic) => {
    //             return (
    //               !_(groupNode.tactics)
    //                 .some(function(node) {
    //                 return (node.tactic === tactic);
    //               })
    //               );
    //           })
    //           .map(
    //           (tactic) => {
    //             return function() {
    //               return self.runTactic(tactic, groupNode);
    //             }
    //           })
    //           .flatten(true)
    //           .value()
    //         );
    //     })
    //       .flatten<() => Promise<any>>(true)
    //       .value()
    //       ;
    //
    //     // flushes the worklist and add the new sparks
    //     this.tacticsWorklist = groupSparks;
    // */
    // //console.log("REPOPULATING TACTICS WORKLIST", this.tacticsWorklist);
    //
    // this.processTactics();
  }

  resize(width: number, height: number) {
    this.width = width;
    this.height = height;
    this.svg
      .style("width", width + "px")
      .style("height", height + "px")
      // also need these as attributes for svg_todataurl
      .attr("width", width + "px")
      .attr("height", height + "px")
      ;
    this.update();
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
    /*
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

              //let unfocusedBefore = getResponseUnfocused(beforeResponse);
              //let unfocusedAfter = getResponseUnfocused(response);
              let newChild = new Tactic(
                t,
                groupToAttachTo,
                response
              );

              // only attach the newChild if it produces something
              // unique from existing children
              let newChildRepr = tacticUnicityRepr(newChild);

              let resultAlreadyExists =
                _(parentGoal.getTactics()).some(function(t) {
                  return t.tactic === newChild.tactic;
                  //return (tacticUnicityRepr(t) === newChildRepr);
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
    */
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
      throw ["shiftNextByTacticGroup", n];
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
      throw ["shiftPrevByTacticGroup", n];
    }
  }

  update(): Promise<{}> {
    let self = this;
    return new Promise(function(onFulfilled, onRejected) {
      return self.updatePromise(onFulfilled, onRejected);
    });
  }

  updatePromise<T>(onFulfilled: () => T, onRejected: () => void): T {
    let self = this;
    let curNode = self.curNode;

    self.resetSVGTransform(); // cancel view transformations

    let nodes = self.tree.nodes(self.rootNode);
    let links = self.tree.links(nodes);
    // now remove all fake nodes
    nodes = _(nodes)
      .filter(function(node) { return !(node instanceof FakeNode); })
      .value()
      ;
    links = _(links)
      .filter(function(link) {
        return !(link.source instanceof FakeNode || link.target instanceof FakeNode)
      })
      .value()
      ;

    // we build the foreignObject first, as its dimensions will guide the others
    let textSelection = self.textLayer
      .selectAll(function() {
        return this.getElementsByTagName("foreignObject");
      })
      .data(nodes, function(d) { return d.id || (d.id = _.uniqueId()); })
      ;

    let textEnter = textSelection.enter()
      .append("foreignObject")
      .classed("monospace", true)
      // the goal nodes need to be rendered at fixed width goalWidth
      // the tactic nodes will be resized to their actual width later
      .attr("width", function(d) {
        return d instanceof GoalNode ? self.getGoalWidth() : self.getTacticWidth();
      })
      ;

    textEnter
      .append("xhtml:body")
      // nodes must know their element to computer their own size
      .each(function(d) {
        d.setHTMLElement(<HTMLElement><any>d3.select(this).node());
      })
      //.classed("svg", true)
      .style("margin", 0) // keep this line for svg_datatourl
      .style("padding", function(d) {
        return d instanceof GoalNode ? goalBodyPadding + "px" : "0px 0px";
      })
      .style("background-color", "transparent")
      // should make it less painful on 800x600 videoprojector
      // TODO: fix computing diffs so that zooming is possible
      .style("font-size", (self.width < 1000) ? "12px" : "14px")
      .style("font-family", "monospace")
      .each(function(d) {
        let jqBody = $(d3.select(this).node());

        /*
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
        */

        if (d instanceof GoalNode) { jqBody.append(d.html); }
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
        }/* else if (d instanceof GoalNode) {
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
          }*/
      })
      // preset the width to update measures correctly
      .attr("width", (d) => d.getWidth())
      .attr("height", 0)
      ;

    // Now that the nodes have a size, we can compute the factors
    self.computeXYFactors();

    // compute how much descendants must be moved to center current
    self.computeDescendantsOffset();

    d3.transition().duration(animationDuration).each(function() {

      // now we need to set the x and y attributes of the entering foreignObjects,
      // so we need to reuse the selection
      textEnter
        .attr("x", function(d) { return d.getOriginalScaledX(); })
        .attr("y", function(d) { return d.getOriginalScaledY(); })
        ;

      textSelection
        .each(function(d) {
          d.cX = nodeX(d) * self.xFactor + self.xOffset(d);
          d.cY = nodeY(d) * self.yFactor + self.yOffset(d);
        })
        // preset the width to update measures correctly
        .attr("width", function(d) { return d.getWidth(); })
        .attr("height", function(d) { return d.getHeight(); })
        .transition()
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
        .attr("x", function(d) {
          // in general, nodes should move towards the parent goal node
          if (!d.hasParent() || self.isRootNode(d)) {
            return d.cX;
          }
          if (d instanceof GoalNode) {
            let nodeToReach = fromJust(d.getGrandParent());
            d.cX = nodeToReach.cX;
            d.cY = nodeToReach.cY;
          } else {
            let nodeToReach = fromJust(d.getParent());
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
      self.onRectSelectionEnter(rectSelection.enter());

      rectSelection
        .classed("current", function(d) { return self.isCurNode(d); })
        .style("stroke", function(d) {
          return self.isCurNode(d) ? "#03C03C" : "";
        })
        .style("stroke-width", function(d) {
          return self.isCurNode(d) ? "4px" : "";
        })
        .classed("solved", function(d) { return d.isSolved(); })
        .transition()
        .style("opacity", "1")
        .attr("width", function(d) { return d.getWidth(); })
        .attr("height", function(d) { return d.getHeight() / self.getCurrentScale(); })
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
        ;

      rectSelection.exit()
        .transition()
        .attr("x", function(d) { return d.cX; })
        .attr("y", function(d) { return d.cY; })
        .style("opacity", "0")
        .remove()
        ;

      let linkSelection = self.linkLayer.selectAll("path").data(links, byLinkId);

      linkSelection.enter()
        .append("path")
        .classed("link", true)
        .attr("fill", "none")
        .attr("d",
        (d: ProofTreeLink) => {
          //let src = swapXY(centerRight0(d.source));
          //let tgt = swapXY(centerLeft0(d.target));
          //return self.diagonal({ "source": src, "target": tgt });
          return diagonal0({ "source": d.source, "target": d.target });
        })
        .attr("stroke",
        (d: ProofTreeLink) => {
          let t = d.target;
          if (
            t instanceof TacticGroupNode
            && fromJust(t.getFocusedTactic()).goals.length === 0
          ) {
            return "#00FF00";
          } else {
            return "#000000";
          }
        })
        ;

      linkSelection
        .transition()
        .style("opacity", 1)
        .attr("d",
        (d) => {
          return diagonal({ "source": d.source, "target": d.target });
        })
        .attr("stroke-width", self.linkWidth.bind(self))
        ;

      linkSelection.exit()
        .transition()
        .attr("d", function(d) {
          return diagonal({ "source": d.source, "target": d.target });
        })
        .style("opacity", "0")
        .remove()
        ;

      /*
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
                    //             .attr("x", rect.left)
                    //             .attr("y", rect.top)
                    //         ;
                    //     })
                    //         ;

                  }

                  leftY0 = elmtRect0(gp, oldHyp.div).bottom;
                  leftY = elmtRect(gp, oldHyp.div).bottom;


                    we don't want to move the right cursor if the
                    right hypothesis was not the very next
                    hypothesis. this happens when a hypothesis gets
                    moved down the list of hypotheses.


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
      */

      // refocus the viewport

      self.viewportX = - (
        curNode.getParent().caseOf({
          // TODO: could do some math to align it the same way
          nothing: () => curNode.cX,
          just: (p) => p.cX,
        })
      );

      self.viewportY = - (
        curNode.cY
        + curNode.getHeight() / 2
        - self.height / 2
      );

      self.viewport
        .transition()
        .attr("transform",
        "translate(" + self.viewportX + ", " + self.viewportY + ")"
        )
        ;

    });

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
      //d.originalScaledX = d.cX;
      //d.originalScaledY = d.cY;
    });

    //this.updateDebug();

    return onFulfilled();

  }

  xOffset(d: ProofTreeNode): number {
    return - d.nodeWidth() / 2; // position the center
  }

  yOffset(d: ProofTreeNode): number {
    let offset = - d.getHeight() / 2; // for the center
    let focusedChild = this.curNode.getFocusedChild();

    // all tactic nodes are shifted such that the current tactic is centered
    //assert(isGoal(this.curNode), "yOffset assumes the current node is a goal!");
    if (this.isCurGoalChild(d)) {
      //assert(focusedChild !== undefined, "yOffset: focusedChild === undefined");
      return offset + (
        nodeY(fromJust(d.getParent())) - nodeY(fromJust(focusedChild))
      ) * this.yFactor;
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

function mkDiagonal(cL, cR) {
  return (
    d3.svg
      .diagonal()
      .source((d: ProofTreeLink, i: number) => {
        return swapXY(cR(d.source));
      })
      .target((d: ProofTreeLink, i: number) => {
        return swapXY(cL(d.target));
      })
      .projection(function(d) { return [d.y, d.x]; })
  );
}

let diagonal0 = mkDiagonal(centerLeft0, centerRight0);
let diagonal = mkDiagonal(centerLeft, centerRight);

function commonAncestor(n1: ProofTreeNode, n2: ProofTreeNode): ProofTreeNode {
  return n1.getParent().caseOf({
    nothing: () => n1,
    just: (n1p) => n2.getParent().caseOf({
      nothing: () => n2,
      just: (n2p) => {
        if (n1.id === n2.id) { return n1; }
        if (n1.depth < n2.depth) {
          return commonAncestor(n1, n2p);
        } else if (n1.depth > n2.depth) {
          return this.commonAncestor(n1p, n2);
        } else {
          return this.commonAncestor(n1p, n2p);
        }
      }
    })
  });
}
