type ProofTreeLink = d3.svg.diagonal.Link<IProofTreeNode>;

interface TacticGroup {
  name: string;
  tactics: string[];
}

interface IStrictly { }

interface IProofTree {
  curNode: IGoalNode;
  rootNode: IGoalNode;
  tacticWaiting: Maybe<string>;
  xFactor: number;
  yFactor: number;
  getAllGoals(): IGoalNode[];
  getGoalWidth(): number;
  getTacticWidth(): number;
  isCurNode(n: IProofTreeNode): boolean;
  isCurNodeAncestor(strictly: IStrictly, n: IProofTreeNode): boolean;
  resize(w: number, h: number);
  update(): Promise<{}>;
  xOffset(n: IProofTreeNode): number;
  yOffset(n: IProofTreeNode): number;
}

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

interface IFakeNode extends IProofTreeNode {
  //constructor(p: IProofTree, n: IProofTreeNode);
}

interface IGoalNode extends IProofTreeNode {
  // constructor(
  //   IProofTree: IProofTree, parent: Maybe<ITacticGroupNode>, goals: IGoals, goal: IPeaCoqGoal
  // );
  context: PeaCoqContext;
  fgIndex: number;
  html: JQuery;
  // stateIds: number[];
  tacticGroups: ITacticGroupNode[];
  addStateId(s: StateId): void;
  getGoalAncestors(): IGoalNode[];
  getTactics(): ITactic[];
  getStateIds(): StateId[];
  onChildSolved(sid: number): void;
  onSolved(sid: number): void;
  removeStateIds(sids: StateId[]): void;
}

interface ITactic {
  goalIndex: number;
  goals: IGoalNode[];
  parentGroup: ITacticGroupNode;
  tactic: string;
  isSolved(): boolean;
}

interface ITacticGroupNode extends IProofTreeNode {
  //constructor(proofTree: IProofTree, parent: IGoalNode, name: string);
  isProcessed: boolean;
  name: string;
  span: JQuery;
  tacticIndex: number;
  tactics: ITactic[];
  getTactics(): ITactic[];
  onChildSolvedAndUnfocused(sid: number): void;
  shiftNextInGroup(): void;
  shiftPrevInGroup(): void;
  updateNode(): void;
}

declare type WorklistItem = () => Promise<TacticGroup[]>;
declare type XY = { x: number; y: number; }

interface Hypothesis {
  div: HTMLElement;
  hName: string;
  hValue: string;
  hType: string;
}
