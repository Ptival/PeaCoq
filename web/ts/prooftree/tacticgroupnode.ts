import { ProofTreeNode } from "./prooftreenode";
import { Strictly } from "../peacoq/strictly";

let userTacticsGroupName = "PeaCoq user tactics";

export class TacticGroupNode extends ProofTreeNode implements ITacticGroupNode {
  isProcessed: boolean;
  // do not use parent, D3 will overwrite
  span: JQuery;
  tacticIndex: number;
  tactics: ITactic[];

  constructor(
    proofTree: IProofTree,
    private parentGoal: IGoalNode,
    public name: string
  ) {
    super(proofTree, just(parentGoal));
    this.isProcessed = false;
    this.tactics = [];
    this.tacticIndex = 0;
  }

  click() {
    alert("TODO: click");
  }

  getAllDescendants(): IProofTreeNode[] {
    let children: IGoalNode[] = _(this.tactics).map(t => t.goals).flatten<IGoalNode>().value();
    let descendants: IProofTreeNode[] = _(children).map(c => c.getAllDescendants()).flatten<IProofTreeNode>().value();
    return [].concat(children, descendants);
  }

  getAllGoalDescendants(): IGoalNode[] {
    let children: IGoalNode[] = _(this.tactics).map(t => t.goals).flatten<IGoalNode>().value();
    let descendants: IGoalNode[] = _(children).map(c => c.getAllGoalDescendants()).flatten<IGoalNode>().value();
    return [].concat(children, descendants);
  }

  getFocusedChild(): Maybe<IProofTreeNode> {
    let viewChildren: IProofTreeNode[] = this.getViewChildren();
    if (viewChildren.length === 0) { return nothing(); }
    return just(viewChildren[this.tactics[this.tacticIndex].goalIndex]);
  }

  getFocusedTactic(): Maybe<ITactic> {
    return (
      this.tactics.length === 0
        ? nothing()
        : just(this.tactics[this.tacticIndex])
    );
  }

  getGoalAncestor(): Maybe<IGoalNode> { return just(this.parentGoal); }

  getHeight(): number {
    let rect = this.getHTMLElement().getBoundingClientRect();
    return Math.ceil(rect.height);
  }

  getParent(): Maybe<IGoalNode> { return just(this.parentGoal); }

  getParentGoal(): IGoalNode { return this.parentGoal; }

  getTactics(): ITactic[] {
    return this.tactics;
  }

  getViewChildren(): IGoalNode[] {
    if (this.isSolved()
      && !this.proofTree.isCurNodeAncestor(Strictly.Yes, this)) {
      return [];
    }
    if (this.tactics.length === 0) { return []; }
    let focusedTactic = this.tactics[this.tacticIndex];
    return focusedTactic.goals;
  }

  getWidth(): number {
    return this.proofTree.getTacticWidth();
  }

  isSolved(): boolean {
    return this.getFocusedTactic().caseOf({
      nothing: () => false,
      just: t => this.isProcessed && t.isSolved(),
    });
  }

  onChildSolvedAndUnfocused(sid: number): void {
    let focusedTactic = fromJust(this.getFocusedTactic());
    let unsolved = <IGoalNode | undefined>_(focusedTactic.goals)
      .find(function(elt) {
        return !elt.isSolved();
      });
    // debugger;
    // console.log("unsolved", unsolved);
    if (unsolved === undefined) {
      this.onSolved(sid);
    } else {
      unsolved.addStateId(sid);
      this.proofTree.curNode = unsolved;
      //this.proofTree.refreshTactics();
      this.proofTree.update();
    }
  }

  onSolved(sid: number): void {
    let self = this;
    this.proofTree.curNode = this.parentGoal;
    this.proofTree.update()
      .then(function() {
        // console.log("THEN");
        self.parentGoal.onChildSolved(sid);
      })
      ;
  }

  shiftNextInGroup() {
    if (this.tacticIndex < this.tactics.length - 1) {
      this.tacticIndex++;
      //asyncLog("NEXTGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]));
      this.proofTree.update();
    }
  }

  shiftPrevInGroup() {
    if (this.tacticIndex > 0) {
      this.tacticIndex--;
      //asyncLog("PREVGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]));
      this.proofTree.update();
    }
  }

  updateNode(): void {
    let jqBody = $(this.getHTMLElement());
    let jQContents;
    let focusedTactic = this.tactics[this.tacticIndex];
    let nbTactics = this.tactics.length;

    this.span = $("<div>")
      .addClass("tacticNode")
      .css("padding", "4px")
      .css("text-align", "center")
      ;

    // prepend a tactic node selector if necessary
    if (nbTactics > 1) {

      if (this.tacticIndex > 0) {
        this.span.append(
          $("<a>")
            .attr("href", "#")
            .text('◀')
            .click(function(e) {
              e.stopImmediatePropagation();
              this.shiftPrevInGroup();
            })
        );
      } else {
        this.span.append(nbsp);
      }

      this.span.append(
        '[' + (this.tacticIndex + 1) + '/' + this.tactics.length + ']'
      );

      if (this.tacticIndex < this.tactics.length - 1) {
        this.span.append(
          $("<a>")
            .attr("href", "#")
            .text('▶')
            .click(function(e) {
              e.stopImmediatePropagation();
              this.shiftNextInGroup();
            })
        );
      } else {
        this.span.append(nbsp);
      }

      this.span.append($("<br>"));

    }

    this.span.append(
      focusedTactic.tactic
    );

    jQContents = this.span;
    jqBody.empty();
    jqBody.append(jQContents);
  }

}
