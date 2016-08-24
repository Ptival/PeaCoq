import { GoalNode } from "./goalnode";
import { ProofTree } from "./prooftree";
import { Tactic } from "./tactic";
import { TacticGroupNode } from "./tacticgroupnode";

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

  const trimmed = CoqStringUtils.coqTrim(query);

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
          nothing(),
          context,
          0
        );
        // pt.curNode$.subscribe(
        //   n => console.log("Current node changed to", n),
        //   null,
        //   () => console.log("No longer tracking current node for this tree")
        // );
        doc.proofTrees.push(pt);
        const g = pt.rootNode;
        g.addStateId(stateId);
        pt.curNode = g;
        pt.update();
      });
    return;
  } else {
    // multiple trees might have been finished at once?
    if (_(["Qed.", "Defined.", "Abort."]).includes(trimmed)) {
      doc.proofTrees.pop();
      if (doc.proofTrees.length === 0) {
        $("#prooftree").empty();
        hideProofTreePanel();
      }
    }
    // while (doc.proofTrees.length > status.statusAllProofs.length) {
    //   doc.proofTrees.shift();
    //   if (doc.proofTrees.length === 0) {
    //     $("#prooftree").empty();
    //     hideProofTreePanel();
    //   }
    // }
  }

  if (doc.proofTrees.length === 0) { return; }

  const activeProofTree = doc.proofTrees.peek();
  const curNode = activeProofTree.curNode;

  if (isUpperCase(trimmed[0]) || CoqStringUtils.isBullet(trimmed)) {
    // curNode.goals = goals;
    curNode.addStateId(stateId);
    return;
  }

  let tactic: Tactic = _.find(curNode.getTactics(), t => t.tactic === trimmed);

  const tacticGroup: ITacticGroupNode = (
    tactic
      ? tactic.parentGroup
      : new TacticGroupNode(activeProofTree, curNode, "")
  );

  /*
  We need to figure out which foreground goals are relevant to this tactic node.
  If the number of unfocused goals has changed by running the tactic, the tactic
  must have solved the previous goal and the current foreground goals are the
  remaining ones.
  Otherwise, the delta foreground goals have been created by running the tactic.
  */
  const goalsBefore = curNode.context;
  const goalsAfter = context;
  const nbRelevantGoals =
    goalsBefore.bgGoals.length === goalsAfter.bgGoals.length
      ? goalsAfter.fgGoals.length - (goalsBefore.fgGoals.length - curNode.fgIndex - 1)
      : goalsAfter.fgGoals.length;
  const relevantGoals = context.fgGoals.slice(0, nbRelevantGoals);

  // console.log("nbRelevantGoals", nbRelevantGoals);
  // debugger;

  const goalNodes: IGoalNode[] =
    _(_.range(nbRelevantGoals))
      .map(ndx =>
        new GoalNode(
          activeProofTree,
          just(tacticGroup),
          context,
          ndx
        )
      )
      .value();

  if (!tactic) {
    curNode.tacticGroups.push(tacticGroup);
    tactic = new Tactic(trimmed, tacticGroup, goalNodes);
    tacticGroup.tactics.push(tactic);
  } else {
    tactic.goals = goalNodes;
  }

  tacticGroup.isProcessed = true;

  if (goalNodes.length > 0) {
    const curGoal: IGoalNode = goalNodes[0];
    curGoal.addStateId(stateId);
    activeProofTree.curNode = curGoal;
    activeProofTree.update();
  } else {
    curNode.onChildSolved(stateId);
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

  if (doc.proofTrees.length === 0) { return; }
  const activeProofTree = doc.proofTrees.peek();
  //lastStateId = sid;
  const curNode = activeProofTree.curNode;

  // clean up necessary for tactics waiting
  activeProofTree.tacticWaiting = nothing();

  // first, get rid of all stored stateIds > sid
  // and mark their children tactic groups unprocessed
  const allGoals = activeProofTree.getAllGoals();

  _(allGoals).each(g => {
    if (_(g.getStateIds()).some(s => _(sids).includes(s))) {
      _(g.tacticGroups).each(g => { g.isProcessed = false; });
    }
    g.removeStateIds(sids);
  });

  // TODO: Not sure if this is always correct
  const target = _.maxBy(allGoals, g => _.max(g.getStateIds()));

  if (target) {
    activeProofTree.curNode = target;
    activeProofTree.update();
  } else {
    // debugger;
    while (doc.proofTrees.length > 0) {
      doc.proofTrees.pop();
    }
    hideProofTreePanel();
    $("#prooftree").empty();
  }

}
