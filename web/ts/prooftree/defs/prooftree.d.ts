interface IProofTree {
    readonly clickOnAncestor$ : Rx.Observable<{}>
    readonly clickOnDescendant$ : Rx.Observable<ITactic>
    readonly curNode: IGoalNode
    readonly curNode$: Rx.Observable<IGoalNode>
    readonly descendantsOffset: number
    // readonly document: ICoqDocument
    readonly rootNode: IGoalNode
    readonly tacticWaiting: Maybe<string>
    readonly xFactor: number
    readonly yFactor: number

    cleanup(): void
    createGoalNode(parent : Maybe<ITacticGroupNode>, context : PeaCoqContext, index : number) : IGoalNode
    getAllGoals(): IGoalNode[]
    getGoalWidth(): number
    getHierarchyCurNode(): d3.HierarchyPointNode<IProofTreeNode>
    getTacticWidth(): number
    linkWidth(d: ProofTreeTypes.Link): string
    isCurNode(n: IProofTreeNode): boolean
    isCurNodeAncestor(strictly: IStrictly, n: IProofTreeNode): boolean
    requestNext(): void
    resize(w: number, h: number): void
    setCurrentNode(n : IGoalNode) : void
    setTacticWaiting(t : string) : void
    unsetTacticWaiting() : void
    scheduleUpdate(): void
    updateAndWait(): Promise<{}>
    // xOffset(n: IProofTreeNode): number
    // yOffset(n: IProofTreeNode): number
}
