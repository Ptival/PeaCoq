interface IProofTreeNode {
    currentScaledX : number
    currentScaledY : number
    readonly depth : number
    readonly id : string
    // label: string
    readonly proofTree : IProofTree
    // x: number
    // x0: number
    // y: number
    // y0: number

    click(): void
    focus(): void
    getAllDescendants(): IProofTreeNode[]
    getAllGoalDescendants(): IGoalNode[]
    getFocusedChild(): Maybe<IProofTreeNode>
    getGoalAncestor(): Maybe<IGoalNode>
    getHeight(): number
    getHTMLElement(): HTMLElement
    // getOriginalScaledX(): number
    // getOriginalScaledY(): number
    getParent(): Maybe<IProofTreeNode>
    // getDestinationScaledX(): number
    // getDestinationScaledY(): number
    getViewChildren(): IProofTreeNode[]
    getViewFocusedChild(): Maybe<IProofTreeNode>
    getViewGrandChildren(): IProofTreeNode[]
    getWidth(): number
    hasParent(): boolean
    hasParentSuchThat(pred: (_1: IProofTreeNode) => boolean): boolean
    isCurNode(): boolean
    isCurNodeAncestor(): boolean
    isSolved(): boolean
    setHTMLElement(e: HTMLElement): void
}
