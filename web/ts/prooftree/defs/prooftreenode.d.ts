interface IProofTreeNode {
  //constructor(p: IProofTree, n: Maybe<IProofTreeNode>);
  depth: number;
  id: string;
  label: string;
  proofTree: IProofTree;
  x: number;
  x0: number;
  y: number;
  y0: number;
  focus(): void;
  getAllDescendants(): IProofTreeNode[];
  getAllGoalDescendants(): IGoalNode[];
  getFocusedChild(): Maybe<IProofTreeNode>;
  getGoalAncestor(): Maybe<IGoalNode>
  getHeight(): number;
  getHTMLElement(): HTMLElement;
  getOriginalScaledX(): number;
  getOriginalScaledY(): number;
  getParent(): Maybe<IProofTreeNode>;
  getScaledX(): number;
  getScaledY(): number;
  getViewChildren(): IProofTreeNode[];
  getViewGrandChildren(): IProofTreeNode[];
  getWidth(): number;
  hasParent(): boolean;
  hasParentSuchThat(pred: (_1: IProofTreeNode) => boolean): boolean;
  isCurNodeAncestor(): boolean;
  isSolved(): boolean;
  setHTMLElement(e: HTMLElement): void;
}
