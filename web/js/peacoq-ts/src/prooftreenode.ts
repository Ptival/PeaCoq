declare class GoalNode { };
import { ProofTree } from "./prooftree";
import { nodeX, nodeY } from "./prooftree-utils";

export abstract class ProofTreeNode {
  private body: HTMLElement;
  depth: number;
  id: string;
  label: string;
  proofTree: ProofTree;
  x: number;
  x0: number;
  y: number;
  y0: number;

  constructor(proofTree: ProofTree, parent: TsMonad.Maybe<ProofTreeNode>) {
    this.body = undefined;
    this.depth = parent.caseOf({
      nothing: () => 0,
      just: (parent) => parent.depth + 1,
    });
    this.id = _.uniqueId();
    this.proofTree = proofTree;
  }

  abstract click(): void;

  abstract getAllDescendants(): ProofTreeNode[];
  abstract getAllGoalDescendants(): GoalNode[];
  abstract getFocusedChild(): Maybe<ProofTreeNode>;
  abstract getGoalAncestor(): Maybe<GoalNode>;
  abstract getHeight(): number;

  getHTMLElement(): HTMLElement {
    if (!this.body) {
      console.log("BAD: missing this.body", this);
    }
    //assert(this.body !== undefined, "ProofTreeNode.getHTMLElement");
    return this.body;
  }

  getOriginalScaledX(): number {
    return this.getScaledX();
    // let self = this;
    // return this.getGoalAncestor().caseOf({
    //   // the root needs to spawn somewhere arbitrary: (0, 0.5)
    //   nothing: () => self.proofTree.xOffset(self),
    //   // non-roots are spawned at their parent's (cX0, cY0)
    //   // just: (p) => + $(p.body.parentElement).attr("x"),
    //   just: (p) => self.getScaledX(),
    // });
  }

  getOriginalScaledY(): number {
    return this.getScaledY();
    // let self = this;
    // let tree = this.proofTree;
    // return this.getGoalAncestor().caseOf({
    //   // the root needs to spawn somewhere arbitrary: (0, 0.5)
    //   nothing: () => 0.5 * tree.xOffset(self) + tree.yOffset(self),
    //   // non-roots are spawned at their parent's (cX0, cY0)
    //   // just: (p) => + $(p.body.parentElement).attr("y"),
    //   just: (p) => self.getScaledY(),
    // });
  }

  abstract getParent(): Maybe<ProofTreeNode>;

  getScaledX(): number {
    let tree = this.proofTree;
    return nodeX(this) * tree.xFactor + tree.xOffset(this);
  }

  getScaledY(): number {
    let tree = this.proofTree;
    return nodeY(this) * tree.yFactor + tree.yOffset(this);
  }

  abstract getViewChildren(): ProofTreeNode[];

  getViewGrandChildren(): ProofTreeNode[] {
    return (
      _(this.getViewChildren())
        .map(function(e) { return e.getViewChildren(); })
        .flatten<ProofTreeNode>(true)
        .value()
    );
  }

  abstract getWidth(): number;

  hasGrandParent(): boolean {
    return this.hasParentSuchThat((p) => p.hasParent());
  }

  hasParent(): boolean { return this.hasParentSuchThat(() => true); }

  hasParentSuchThat(pred: (_1: ProofTreeNode) => boolean): boolean {
    return this.getParent().caseOf({
      nothing: () => false,
      just: (p) => pred(p),
    });
  }

  isCurNodeAncestor() {
    let curNode = this.proofTree.curNode;
    let common = commonAncestor(curNode, this);
    return this.id === common.id;
  }

  abstract isSolved(): boolean;
  abstract nodeWidth(): number;

  setHTMLElement(e: HTMLElement): void {
    this.body = e;
  }

}

export function commonAncestor(n1: ProofTreeNode, n2: ProofTreeNode): ProofTreeNode {
  return n1.getParent().caseOf({
    nothing: () => n1,
    just: (n1p) => n2.getParent().caseOf({
      nothing: () => n2,
      just: (n2p) => {
        if (n1.id === n2.id) { return n1; }
        if (n1.depth < n2.depth) {
          return commonAncestor(n1, n2p);
        } else if (n1.depth > n2.depth) {
          return commonAncestor(n1p, n2);
        } else {
          return commonAncestor(n1p, n2p);
        }
      }
    })
  });
}
