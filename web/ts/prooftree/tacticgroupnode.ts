import { ProofTreeNode } from "./prooftreenode"
import { Strictly } from "../peacoq/strictly"
import * as Command from "../sertop/command"
import * as ControlCommand from "../sertop/control-command"

const userTacticsGroupName = "PeaCoq user tactics"

export class TacticGroupNode extends ProofTreeNode implements ITacticGroupNode {
  public isProcessed: boolean
  // do not use parent, D3 will overwrite
  public span: JQuery
  public tacticIndex: number
  public tactics: ITactic[]

  constructor(
    proofTree: IProofTree,
    private parentGoal: IGoalNode,
    public name: string
  ) {
    super(proofTree, just(parentGoal))
    this.isProcessed = false
    this.tactics = []
    this.tacticIndex = 0
  }

  public click() {
    if (this.proofTree.isCurNodeAncestor(Strictly.Yes, this)) {
      const stateId = _.min(this.proofTree.curNode.getStateIds())
      if (stateId === undefined) { debugger }
      this.proofTree.document.sendCommands(
        Rx.Observable.just(new Command.Control(new ControlCommand.StmCancel([stateId])))
      )
    }
    this.getFocusedTactic().caseOf({
      nothing: () => { debugger },
      just: t => {
        this.proofTree.document.editor.execCommand("insertstring", ` ${t.tactic}`)
        this.proofTree.document.next()
        this.proofTree.document.editor.execCommand("insertstring", "\n")
      }
    })
  }

  public focus() {
    this.parentGoal.getFocusedChild().caseOf({
      nothing: () => { },
      just: focused => {
        if (focused.id === this.id) { return }
        const thisIndex = _.findIndex(this.parentGoal.tacticGroups, t => t.id === this.id)
        if (thisIndex === -1) { debugger }
        this.parentGoal.tacticIndex = thisIndex
        this.parentGoal.focus()
      }
    })
  }

  public getAllDescendants(): IProofTreeNode[] {
    const children: IGoalNode[] = _(this.tactics).map(t => t.goals).flatten<IGoalNode>().value()
    const descendants: IProofTreeNode[] = _(children).map(c => c.getAllDescendants()).flatten<IProofTreeNode>().value()
    return ([] as IProofTreeNode[]).concat(children, descendants)
  }

  public getAllGoalDescendants(): IGoalNode[] {
    const children: IGoalNode[] = _(this.tactics).map(t => t.goals).flatten<IGoalNode>().value()
    const descendants: IGoalNode[] = _(children).map(c => c.getAllGoalDescendants()).flatten<IGoalNode>().value()
    return ([] as IGoalNode[]).concat(children, descendants)
  }

  public getFocusedChild(): Maybe<IGoalNode> {
    if (this.tactics.length === 0) { return nothing() }
    const focusedTactic = this.tactics[this.tacticIndex]
    if (focusedTactic.goals.length === 0) { return nothing() }
    return just(focusedTactic.goals[focusedTactic.goalIndex])
  }

  public getFocusedTactic(): Maybe<ITactic> {
    return (
      this.tactics.length === 0
        ? nothing()
        : just(this.tactics[this.tacticIndex])
    )
  }

  public getGoalAncestor(): Maybe<IGoalNode> { return just(this.parentGoal) }

  public getHeight(): number {
    const rect = this.getHTMLElement().getBoundingClientRect()
    return Math.ceil(rect.height)
  }

  public getParent(): Maybe<IGoalNode> { return just(this.parentGoal) }

  public getParentGoal(): IGoalNode { return this.parentGoal }

  public getTactics(): ITactic[] {
    return this.tactics
  }

  public getViewChildren(): IGoalNode[] {
    if (this.isSolved()
      && !this.proofTree.isCurNodeAncestor(Strictly.Yes, this)) {
      return []
    }
    if (this.tactics.length === 0) { return [] }
    const focusedTactic = this.tactics[this.tacticIndex]
    return focusedTactic.goals
  }

  public getWidth(): number {
    return this.proofTree.getTacticWidth()
  }

  public isSolved(): boolean {
    return this.getFocusedTactic().caseOf({
      nothing: () => false,
      just: t => this.isProcessed && t.isSolved(),
    })
  }

  public onChildSolvedAndUnfocused(sid: number): void {
    const focusedTactic = fromJust(this.getFocusedTactic())
    const unsolved = <IGoalNode | undefined>_(focusedTactic.goals)
      .find(elt => !elt.isSolved())
    // debugger
    // console.log("unsolved", unsolved)
    if (unsolved === undefined) {
      this.onSolved(sid)
    } else {
      unsolved.addStateId(sid)
      this.proofTree.curNode = unsolved
      // this.proofTree.refreshTactics()
      this.proofTree.scheduleUpdate()
    }
  }

  public onSolved(sid: number): void {
    this.proofTree.curNode = this.parentGoal
    this.proofTree.updateAndWait()
      .then(() => {
        // console.log("THEN")
        this.parentGoal.onChildSolved(sid)
      })

  }

  public shiftNextInGroup() {
    if (this.tacticIndex < this.tactics.length - 1) {
      this.tacticIndex++
      // asyncLog("NEXTGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]))
      this.proofTree.scheduleUpdate()
    }
  }

  public shiftPrevInGroup() {
    if (this.tacticIndex > 0) {
      this.tacticIndex--
      // asyncLog("PREVGROUPFOCUS " + nodeString(this.tactics[this.tacticIndex]))
      this.proofTree.scheduleUpdate()
    }
  }

  public updateNode(): void {
    const jqBody = $(this.getHTMLElement())
    let jQContents: JQuery
    const focusedTactic = this.tactics[this.tacticIndex]
    const nbTactics = this.tactics.length

    this.span = $("<div>")
      .addClass("tacticNode")
      .css("padding", "4px")
      .css("text-align", "center")

    // prepend a tactic node selector if necessary
    if (nbTactics > 1) {

      if (this.tacticIndex > 0) {
        this.span.append(
          $("<a>")
            .attr("href", "#")
            .text("◀")
            .click(e => {
              e.stopImmediatePropagation()
              this.shiftPrevInGroup()
            })
        )
      } else {
        this.span.append(nbsp)
      }

      this.span.append(
        "[" + (this.tacticIndex + 1) + "/" + this.tactics.length + "]"
      )

      if (this.tacticIndex < this.tactics.length - 1) {
        this.span.append(
          $("<a>")
            .attr("href", "#")
            .text("▶")
            .click(e => {
              e.stopImmediatePropagation()
              this.shiftNextInGroup()
            })
        )
      } else {
        this.span.append(nbsp)
      }

      this.span.append($("<br>"))

    }

    this.span.append(
      focusedTactic.tactic
    )

    jQContents = this.span
    jqBody.empty()
    jqBody.append(jQContents)
  }

}
