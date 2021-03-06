interface ITacticGroupNode extends IProofTreeNode {
  //constructor(proofTree: IProofTree, parent: IGoalNode, name: string);
  isProcessed: boolean;
  name: string;
  span: JQuery;
  tacticIndex: number;
  tactics: ITactic[];
  getFocusedChild(): Maybe<IGoalNode>;
  getFocusedTactic(): Maybe<ITactic>;
  getParent(): Maybe<IGoalNode>;
  getTactics(): ITactic[];
  onChildSolvedAndUnfocused(sid: number): void;
  shiftNextInGroup(): void;
  shiftPrevInGroup(): void;
  updateNode(): void;
}
