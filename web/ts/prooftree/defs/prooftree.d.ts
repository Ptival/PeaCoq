interface IProofTree {
  curNode: IGoalNode;
  curNode$: Rx.Observable<IGoalNode>;
  document: ICoqDocument;
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
  requestNext(): void;
  resize(w: number, h: number): void;
  scheduleUpdate(): void;
  updateAndWait(): Promise<{}>;
  xOffset(n: IProofTreeNode): number;
  yOffset(n: IProofTreeNode): number;
}
