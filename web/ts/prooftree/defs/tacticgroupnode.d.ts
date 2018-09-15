interface ITacticGroupNode extends IProofTreeNode {
    readonly click$ : Rx.Observable<{}>
    //constructor(proofTree: IProofTree, parent: IGoalNode, name: string)
    isProcessed: boolean
    readonly name: string
    readonly span: JQuery
    tacticIndex: number
    readonly tactics: ITactic[]

    getFocusedChild(): Maybe<IGoalNode>
    getFocusedTactic(): Maybe<ITactic>
    getParent(): Maybe<IGoalNode>
    getTactics(): ITactic[]
    onChildSolvedAndUnfocused(sid: number): void
    shiftNextInGroup(): void
    shiftPrevInGroup(): void
    updateNode(): void
}
