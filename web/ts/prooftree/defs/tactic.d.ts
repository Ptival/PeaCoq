interface ITactic {
  goalIndex: number;
  goals: IGoalNode[];
  parentGroup: ITacticGroupNode;
  tactic: string;
  isSolved(): boolean;
}
