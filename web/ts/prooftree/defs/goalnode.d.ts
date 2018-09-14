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

    addStateId(s : import('../../coq/lib/stateid').t): void
    addTactic(tacticName : string, groupName : string, context : PeaCoqContext, stateId : import('../../coq/lib/stateid').t) : ITactic
    getFocusedChild() : Maybe<ITacticGroupNode>
    getGoalAncestors() : IGoalNode[]
    getParent() : Maybe<ITacticGroupNode>
    getTactics() : ITactic[]
    getStateIds() : import('../../coq/lib/stateid').t[]
    // findOrCreateGroup(groupName : string) : ITacticGroupNode
    onChildSolved(sid : number) : void
    onSolved(sid : number) : void
    removeStateIds(sids : import('../../coq/lib/stateid').t[]) : void
}
