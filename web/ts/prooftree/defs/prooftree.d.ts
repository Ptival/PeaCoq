interface IProofTree {
  curNode: IGoalNode
  curNode$: Rx.Observable<IGoalNode>
  descendantsOffset: number
  document: ICoqDocument
  rootNode: IGoalNode
  tacticWaiting: Maybe<string>
  xFactor: number
  yFactor: number
  cleanup(): void
  getAllGoals(): IGoalNode[]
  getGoalWidth(): number
  getHierarchyCurNode(): d3.HierarchyPointNode<IProofTreeNode>
  getTacticWidth(): number
  linkWidth(d: ProofTreeTypes.Link): string
  isCurNode(n: IProofTreeNode): boolean
  isCurNodeAncestor(strictly: IStrictly, n: IProofTreeNode): boolean
  requestNext(): void
  resize(w: number, h: number): void
  scheduleUpdate(): void
  updateAndWait(): Promise<{}>
  // xOffset(n: IProofTreeNode): number
  // yOffset(n: IProofTreeNode): number
}
