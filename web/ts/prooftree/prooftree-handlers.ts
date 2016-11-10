import * as _ from "lodash"

import { GoalNode } from "./goalnode"
import { ProofTree } from "./prooftree"
import { Tactic } from "./tactic"
import { TacticGroupNode } from "./tacticgroupnode"

export function proofTreeOnEdit(
  doc: ICoqDocument,
  showProofTreePanel: () => Promise<{}>,
  hideProofTreePanel: () => void,
  query: string,
  stateId: number,
  // lastStatus: IStatus,
  // status: IStatus,
  context: PeaCoqContext
): void {

  const trimmed = CoqStringUtils.coqTrim(query)

  // I used to be smarter about this but I got tired of it
  if (trimmed === "Proof.") {
    // we are behind on the number of proof trees, create one
    showProofTreePanel()
      .then(() => { // needs to be before for width/height
        const pt = new ProofTree(
          "FIXME",
          // status.statusProofName,
          $("#prooftree")[0],
          $("#prooftree").parent().width(),
          $("#prooftree").parent().height(),
          nothing<ITacticGroupNode>(),
          context,
          0,
          doc
        )
        // pt.curNode$.subscribe(
        //   n => console.log("Current node changed to", n),
        //   null,
        //   () => console.log("No longer tracking current node for this tree")
        // )
        doc.proofTrees.push(pt)
        const g = pt.rootNode
        g.addStateId(stateId)
        pt.curNode = g
        pt.scheduleUpdate()
      })
    return
  } else {
    // multiple trees might have been finished at once?
    if (_(["Qed.", "Defined.", "Abort."]).includes(trimmed)) {
      doc.proofTrees.pop()
      if (doc.proofTrees.length === 0) {
        $("#prooftree").empty()
        hideProofTreePanel()
      }
    }
    // while (doc.proofTrees.length > status.statusAllProofs.length) {
    //   doc.proofTrees.shift()
    //   if (doc.proofTrees.length === 0) {
    //     $("#prooftree").empty()
    //     hideProofTreePanel()
    //   }
    // }
  }

  if (doc.proofTrees.length === 0) { return }

  const activeProofTree = doc.proofTrees.peek()
  const curNode = activeProofTree.curNode

  if (isUpperCase(trimmed[0]) || CoqStringUtils.isBullet(trimmed)) {
    // curNode.goals = goals
    curNode.addStateId(stateId)
    return
  }

  const tactic = curNode.addTactic(trimmed, "", context, stateId)
  tactic.focus()

  tactic.parentGroup.isProcessed = true

  if (tactic.goals.length > 0) {
    const curGoal: IGoalNode = tactic.goals[0]
    curGoal.addStateId(stateId)
    curNode.proofTree.curNode = curGoal
    curNode.proofTree.scheduleUpdate()
  } else {
    curNode.onChildSolved(stateId)
  }

}

/*
  For now, let's just rewind within the tree or give up. Eventually,
  we could rewind into old trees.
 */
export function onStmCanceled(
  doc: ICoqDocument,
  hideProofTreePanel: () => void,
  sids: StateId[]
): void {

  if (doc.proofTrees.length === 0) { return }
  const activeProofTree = doc.proofTrees.peek()
  // lastStateId = sid
  const curNode = activeProofTree.curNode

  // clean up necessary for tactics waiting
  activeProofTree.tacticWaiting = nothing<string>()

  // first, get rid of all stored stateIds > sid
  // and mark their children tactic groups unprocessed
  const allGoals = activeProofTree.getAllGoals()

  _(allGoals).each(g => {
    if (_(g.getStateIds()).some((s: StateId) => _(sids).includes(s))) {
      _(g.tacticGroups).each(g => { g.isProcessed = false })
    }
    g.removeStateIds(sids)
  })

  // TODO: Not sure if this is always correct
  const target = _.maxBy(allGoals, g => _.max(g.getStateIds()))

  if (target) {
    activeProofTree.curNode = target
    activeProofTree.scheduleUpdate()
  } else {
    // debugger
    while (doc.proofTrees.length > 0) {
      doc.proofTrees.pop()
    }
    hideProofTreePanel()
    $("#prooftree").empty()
  }

}
