interface ITactic {
  goalIndex: number;
  goals: IGoalNode[];
  parentGroup: ITacticGroupNode;
  tactic: string;
  focus(): void;
  isSolved(): boolean;
}
