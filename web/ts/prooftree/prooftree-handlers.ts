import * as _ from 'lodash'

import { GoalNode } from './goalnode'
import { ProofTree } from './prooftree'
import { Tactic } from './tactic'
import { TacticGroupNode } from './tacticgroupnode'
import * as StateId from '../coq/lib/stateid'
import * as PeaCoqUtils from '../peacoq/utils'
import * as SerAPIProtocol from '../sertop/serapi-protocol'

export function proofTreeOnEdit(
    doc : ICoqDocument,
    showProofTreePanel : () => Promise<{}>,
    hideProofTreePanel : () => void,
    query : string,
    stateId : number,
    // lastStatus : IStatus,
    // status : IStatus,
    context : PeaCoqContext
) : void {

    const trimmed = CoqStringUtils.coqTrim(query)

    // I used to be smarter about this but I got tired of it: for now, you need
    // the `Proof.` keyword to open the prooftree.
    if (trimmed === 'Proof.') {
        // we are behind on the number of proof trees, create one
        showProofTreePanel()
            .then(() => { // needs to be before for width/height
                const pt = new ProofTree(
                    'FIXME',
                    // status.statusProofName,
                    $('#prooftree')[0],
                    $('#prooftree').parent().width()  || 100,
                    $('#prooftree').parent().height() || 100,
                    context,
                    0,
                    doc
                )

                pt.clickOnAncestor$.subscribe(({}) => {
                    // For now, we only allow clicks on the parent, so we just
                    // need to cancel the current node.  We cancel its lowest
                    // state ID.
                    const stateId = _.min(pt.curNode.getStateIds())
                    if (stateId === undefined) {
                        debugger
                        throw stateId
                    }
                    doc.sendCommands(
                        Rx.Observable.just(new SerAPIProtocol.Cancel([stateId]))
                    )
                })

                pt.clickOnDescendant$.subscribe(t => {
                    doc.editor.execCommand('insertstring', ` ${t.tactic}`)
                    doc.next()
                    doc.editor.execCommand('insertstring', '\n')
                })

                // pt.curNode$.subscribe(
                //   n => console.log('Current node changed to', n),
                //   null,
                //   () => console.log('No longer tracking current node for this tree')
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
        if (_(['Qed.', 'Defined.', 'Abort.']).includes(trimmed)) {
            doc.proofTrees.pop()
            if (doc.proofTrees.length === 0) {
                $('#prooftree').empty()
                hideProofTreePanel()
            }
        }
        // while (doc.proofTrees.length > status.statusAllProofs.length) {
        //   doc.proofTrees.shift()
        //   if (doc.proofTrees.length === 0) {
        //     $('#prooftree').empty()
        //     hideProofTreePanel()
        //   }
        // }
    }

    if (doc.proofTrees.length === 0) { return }

    const activeProofTree = doc.proofTrees.peek()
    const curNode = activeProofTree.curNode

    if (PeaCoqUtils.isUpperCase(trimmed[0]) || CoqStringUtils.isBullet(trimmed)) {
        // curNode.goals = goals
        curNode.addStateId(stateId)
        return
    }

    const tactic = curNode.addTactic(trimmed, '', context, stateId)
    tactic.focus()

    tactic.parentGroup.isProcessed = true

    if (tactic.goals.length > 0) {
        const curGoal : IGoalNode = tactic.goals[0]
        curGoal.addStateId(stateId)
        curNode.proofTree.setCurrentNode(curGoal)
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
    doc : ICoqDocument,
    hideProofTreePanel : () => void,
    sids : StateId.t[]
) : void {

    if (doc.proofTrees.length === 0) { return }
    const activeProofTree = doc.proofTrees.peek()
    // lastStateId = sid
    const curNode = activeProofTree.curNode

    // clean up necessary for tactics waiting
    activeProofTree.unsetTacticWaiting()

    // first, get rid of all stored stateIds > sid
    // and mark their children tactic groups unprocessed
    const allGoals = activeProofTree.getAllGoals()

    _(allGoals).each(g => {
        if (_(g.getStateIds()).some((s : StateId.t) => _(sids).includes(s))) {
            _(g.tacticGroups).each(g => { g.isProcessed = false })
        }
        g.removeStateIds(sids)
    })

    // TODO : Not sure if this is always correct
    const target = _.maxBy(allGoals, g => _.max(g.getStateIds()))

    if (target) {
        activeProofTree.setCurrentNode(target)
        activeProofTree.scheduleUpdate()
    } else {
        // debugger
        while (doc.proofTrees.length > 0) {
            doc.proofTrees.pop()
        }
        hideProofTreePanel()
        $('#prooftree').empty()
    }

}
