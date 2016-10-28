interface ITactic {
  goalIndex: number
  goals: IGoalNode[]
  parentGroup: ITacticGroupNode
  tactic: string
  focus(): void
  getFocusedGoal(): Maybe<IGoalNode>
  isSolved(): boolean
}
