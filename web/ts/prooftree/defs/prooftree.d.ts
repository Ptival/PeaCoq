interface IProofTree {
  curNode: IGoalNode;
  curNode$: Rx.Observable<IGoalNode>;
  rootNode: IGoalNode;
  tacticWaiting: Maybe<string>;
  xFactor: number;
  yFactor: number;
  cleanup(): void;
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
