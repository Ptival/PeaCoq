interface IProofTree {
  curNode: IGoalNode;
  curNode$: Rx.Observable<IGoalNode>;
  cancelSubject: Rx.Subject<StateId>;
  editor: AceAjax.Editor;
  nextSubject: Rx.Subject<{}>;
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
  scheduleUpdate(): void;
  updateAndWait(): Promise<{}>;
  xOffset(n: IProofTreeNode): number;
  yOffset(n: IProofTreeNode): number;
}
