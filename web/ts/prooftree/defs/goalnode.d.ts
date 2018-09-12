interface IGoalNode extends IProofTreeNode {
    // constructor(
    //   IProofTree: IProofTree, parent: Maybe<ITacticGroupNode>, goals: IGoals, goal: IPeaCoqGoal
    // )
    context : PeaCoqContext
    fgIndex : number
    html : JQuery
    // stateIds : number[]
    tacticIndex : number
    tacticGroup$ : Rx.Observable<ITacticGroupNode>
    tacticGroups : ITacticGroupNode[]

    addStateId(s : StateId): void
    addTactic(tacticName : string, groupName : string, context : PeaCoqContext, stateId : StateId) : ITactic
    getFocusedChild() : Maybe<ITacticGroupNode>
    getGoalAncestors() : IGoalNode[]
    getParent() : Maybe<ITacticGroupNode>
    getTactics() : ITactic[]
    getStateIds() : StateId[]
    // findOrCreateGroup(groupName : string) : ITacticGroupNode
    onChildSolved(sid : number) : void
    onSolved(sid : number) : void
    removeStateIds(sids : StateId[]) : void
}
