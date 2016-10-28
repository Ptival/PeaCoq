import { Tactic } from "./tactic"
import { TacticGroupNode } from "./tacticgroupnode"
import { ProofTreeNode } from "./prooftreenode"
import { Strictly } from "../peacoq/strictly"

export class GoalNode extends ProofTreeNode implements IGoalNode {
  // DO NOT USE "children" AS D3 WILL OVERWRITE
  private closedBraces: number
  public html: JQuery
  private openBraces: number
  // DO NOT USE "parent" AS D3 WILL OVERWRITE
  private parentGroup: Maybe<ITacticGroupNode>
  private stateIds: number[]
  public tacticGroups: ITacticGroupNode[]
  private _tacticIndex: number

  constructor(
    proofTree: IProofTree,
    parent: Maybe<ITacticGroupNode>,
    public context: PeaCoqContext,
    public fgIndex: number
  ) {
    super(proofTree, parent)
    // debugger
    this.closedBraces = 0
    this.html = $("<div>")
      .attr("id", _.uniqueId())
      .append(this.context.fgGoals[this.fgIndex].ppgoal.getHTML())

    this.openBraces = 0
    this.parentGroup = parent
    this.stateIds = []
    this.tacticGroups = []
    this._tacticIndex = 0
  }

  get tacticIndex(): number { return this._tacticIndex }
  set tacticIndex(ti: number) {
    if (ti >= this.tacticGroups.length) { debugger }
    this._tacticIndex = ti
  }

  public addStateId(s: StateId): void {
    // console.log("Adding state ID", s)
    this.stateIds.push(s)
  }

  public addTactic(tacticName: string, groupName: string, context: PeaCoqContext, stateId: StateId): ITactic {
    const found = _.find(this.getTactics(), t => t.tactic === tacticName)
    if (found !== undefined) {
      return found
    }

    let tacticGroup = _.find(this.tacticGroups, tg => tg.name === groupName)
    if (tacticGroup === undefined) {
      tacticGroup = new TacticGroupNode(this.proofTree, this, groupName)
      this.tacticGroups.push(tacticGroup)
    }

    /*
    We need to figure out which foreground goals are relevant to this tactic node.
    If the number of unfocused goals has changed by running the tactic, the tactic
    must have solved the previous goal and the current foreground goals are the
    remaining ones.
    Otherwise, the delta foreground goals have been created by running the tactic.
    */
    const goalsBefore = this.context
    const goalsAfter = context
    const nbRelevantGoals =
      goalsBefore.bgGoals.length === goalsAfter.bgGoals.length
        ? goalsAfter.fgGoals.length - (goalsBefore.fgGoals.length - this.fgIndex - 1)
        : goalsAfter.fgGoals.length
    const relevantGoals = context.fgGoals.slice(0, nbRelevantGoals)

    // console.log("nbRelevantGoals", nbRelevantGoals)
    // debugger

    const goalNodes: IGoalNode[] =
      _(_.range(nbRelevantGoals))
        .map(ndx =>
          new GoalNode(
            this.proofTree,
            just(tacticGroup),
            context,
            ndx
          )
        )
        .value()

    const newTactic = new Tactic(tacticName, tacticGroup, goalNodes)
    tacticGroup.tactics.push(newTactic)
    return newTactic

  }

  public click(): void { return }

  // findOrCreateGroup(groupName: string): ITacticGroupNode {
  //   const found = <ITacticGroupNode | undefined>_(this.tacticGroups)
  //     .find(function(tacticGroup) {
  //       return tacticGroup.name === groupName
  //     })
  //   if (found !== undefined) { return found; }
  //   // else, create it
  //   const groupNode = new TacticGroupNode(this.proofTree, this, groupName)
  //   this.tacticGroups.push(groupNode)
  //   return groupNode
  // }

  public focus(): void {
    this.parentGroup.fmap(tg => {
      const tacticIndex = _.findIndex(tg.tactics, t => _.some(t.goals, g => g.id === this.id))
      if (tacticIndex === -1) { debugger }
      tg.tacticIndex = tacticIndex
      const tactic = tg.tactics[tg.tacticIndex]
      const goalIndex = _.findIndex(tactic.goals, g => g.id === this.id)
      if (goalIndex === -1) { debugger }
      tactic.goalIndex = goalIndex
      tg.focus()
    })
  }

  public getAllDescendants(): IProofTreeNode[] {
    const children: ITacticGroupNode[] = this.tacticGroups
    const descendants: IProofTreeNode[] = _(children).map(c => c.getAllDescendants()).flatten<IProofTreeNode>().value()
    return ([] as IProofTreeNode[]).concat(children, descendants)
  }

  public getAllGoalDescendants(): GoalNode[] {
    const children: ITacticGroupNode[] = this.tacticGroups
    const descendants: GoalNode[] = _(children).map(c => c.getAllGoalDescendants()).flatten<GoalNode>().value()
    const result: GoalNode[] = [this]
    return result.concat(descendants)
  }

  public getFocusedChild(): Maybe<ITacticGroupNode> {
    if (this.tacticGroups.length === 0) { return nothing<ITacticGroupNode>() }
    return just(this.tacticGroups[this.tacticIndex])
  }

  public getGoalAncestor(): Maybe<IGoalNode> {
    return this.parentGroup.bind(g => g.getGoalAncestor())
  }

  public getFocusedTacticGroup(): TsMonad.Maybe<ITacticGroupNode> {
    const nonEmptyTacticGroups: ITacticGroupNode[] = _(this.tacticGroups)
      .filter(group => group.tactics.length > 0)
      .value()

    if (nonEmptyTacticGroups.length === 0) { return TsMonad.Maybe.nothing<ITacticGroupNode>() }
    return TsMonad.Maybe.just(nonEmptyTacticGroups[this.tacticIndex])
  }

  public getGoalAncestors(): IGoalNode[] {
    return this.getGrandParent().caseOf<IGoalNode[]>({
      nothing: () => [this],
      just: gp => ([] as IGoalNode[]).concat([this], gp.getGoalAncestors()),
    })
  }

  public getGrandParent(): Maybe<IGoalNode> {
    return this.parentGroup.caseOf({
      nothing: () => nothing<IGoalNode>(),
      just: (p: ITacticGroupNode) => p.getParent(),
    })
  }

  public getHeight(): number {
    const node = this.getHTMLElement()
    const rect = node.getBoundingClientRect()
    return Math.ceil(rect.height)
  }

  public getParent(): Maybe<ITacticGroupNode> { return this.parentGroup }

  public getStateIds(): StateId[] {
    return this.stateIds
  }

  public getTactics(): ITactic[] {
    return _(this.tacticGroups)
      .map(g => g.getTactics())
      .flatten<ITactic>(true)
      .value()
  }

  /*
   * [getViewChildren] returns the children of the considered node in the current
   * view. If the node is collapsed, it needs to have one child if it is an
   * ancestor of the current node, so that the current node is reachable.
   */
  public getViewChildren(): ITacticGroupNode[] {
    if (this.isSolved()
      && !this.proofTree.isCurNodeAncestor(Strictly.Yes, this)) {
      return []
    }
    // const nonEmptyTacticGroups = _(this.tacticGroups)
    //   .filter(function(group) { return (group.tactics.length > 0); })
    //   .value()
    //   
    if (this.tacticGroups.length === 0) { return [] }
    if (this.proofTree.isCurNode(this)) {
      return this.tacticGroups
    } else if (this.isCurNodeAncestor()) {
      return [this.tacticGroups[this.tacticIndex]]
    } else {
      return []
    }
  }

  public getViewFocusedChild(): Maybe<ITacticGroupNode> {
    const viewChildren = this.getViewChildren()
    return this.getFocusedTacticGroup()
      .bind(tacticGroup => {
        const found = viewChildren.find(e => e.id === tacticGroup.id)
        if (found === undefined) { return nothing<ITacticGroupNode>() }
        return just(found)
      })
  }

  public getWidth(): number {
    return this.proofTree.getGoalWidth()
  }

  public isSolved(): boolean {
    if (this.proofTree.isCurNodeAncestor(Strictly.Yes, this)) { return false }
    const focusedTacticGroup = this.getFocusedTacticGroup()
    return this.getFocusedTacticGroup().caseOf({
      nothing: () => false,
      just: tg => tg.isSolved(),
    })
  }

  public onChildSolved(sid: number): void {
    this.onSolved(sid)
  }

  public onSolved(sid: number): void {
    if (this.openBraces === this.closedBraces) {
      this.parentGroup.caseOf({
        nothing: () => {
          // if (autoLayout) {
          //   //proofTreeQueryWish('Qed.')
          // }
        },
        just: p => p.onChildSolvedAndUnfocused(sid),
      })
    }
    //  else if (autoLayout) {
    //   //proofTreeQueryWish('}')
    // }
  }

  public removeStateIds(sids: StateId[]): void {
    // console.log("Removing state IDs", sids, "from", this.stateIds)
    this.stateIds = _(this.stateIds).filter(s => !_(sids).includes(s)).value()
    // console.log("Remaining", this.stateIds)
  }

}
