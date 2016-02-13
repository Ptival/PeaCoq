$(document).ready(() => {
  peaCoqAddHandlers.push(proofTreeOnAdd);
  peaCoqGetContextHandlers.push(proofTreeOnGetContext);
  peaCoqEditAtHandlers.push(proofTreeOnEditAt);
  //peaCoqGoalHandlers.push(proofTreeOnGoal);
  peaCoqStatusHandlers.push(proofTreeOnStatus);
});

/*
We only react to commands that look like tactics. For now, the
heuristic is that it does not start with an uppercase character.
To take into account the command, we lookup whether this command
was expected (for instance, if the tree mode asked for it).
If it already existed or was expected, nothing is done.
If it was unexpected, let's create an empty, nameless group to hold it.
*/
function proofTreeOnAdd(s: string, r: AddReturn): void {
  if (proofTrees.length === 0) { return; }
  let activeProofTree = proofTrees[0];
  activeProofTree.stateId = r.stateId;
  let curNode = activeProofTree.curNode;
  let trimmed = coqTrim(s);

  if (isUpperCase(trimmed[0])) { return; }

  if (curNode instanceof GoalNode) {
    let existingTactic = _(curNode.getTactics())
      .find(function(elt) { return elt.tactic === coqTrim(s); })
      ;
    if (existingTactic === undefined) {
      let tg = new TacticGroupNode(activeProofTree, curNode, "");
      curNode.tacticGroups.push(tg);
      let t = new Tactic(coqTrim(s), tg, r);
      activeProofTree.tacticWaitingForContext = t;
      tg.tactics.push(t);
    } else {
      activeProofTree.tacticWaitingForContext = existingTactic;
    }
    activeProofTree.update();
  }
}

/*
  For now, let's just rewind within the tree or give up. Eventually,
  we could rewind into old trees.
 */
function proofTreeOnEditAt(sid: number): void {
  if (proofTrees.length === 0) { return; }
  let activeProofTree = proofTrees[0];
  let curNode = activeProofTree.curNode;
  if (curNode instanceof GoalNode) {
    let ancestorGoals = curNode.getGoalAncestors();
    let target = _(ancestorGoals).find((g) => {
      return g.stateId === sid;
    });
    if (target) {
      activeProofTree.curNode = target;
      activeProofTree.update();
      if (activeProofTree.tacticWaitingForContext) {
        throw "TODO: proofTreeOnEditAt tactic waiting to be cleared";
      }
    } else {

    }
  } else {
    throw "TODO: proofTreeOnEditAt";
  }
}

function proofTreeOnGetContext(c: PeaCoqContext): void {
  if (proofTrees.length === 0) { return; }
  let activeProofTree = proofTrees[0];
  let curNode = activeProofTree.curNode;
  let tacticWaiting = activeProofTree.tacticWaitingForContext;
  // TODO: Cover all goals rather than just the first :)
  if (!curNode) {
    let g = new GoalNode(activeProofTree, undefined, c[0]);
    g.stateId = activeProofTree.stateId;
    activeProofTree.curNode = g;
    activeProofTree.update();
  }
  if (tacticWaiting) {
    let g = new GoalNode(activeProofTree, tacticWaiting.parentGroup, c[0]);
    // the first goal's stateId is known
    g.stateId = activeProofTree.stateId;
    tacticWaiting.goals = [g];
    activeProofTree.tacticWaitingForContext = undefined;
    activeProofTree.curNode = g;
    activeProofTree.update();
  }
}

function proofTreeOnStatus(s: Status): void {
  // hopefully we are always at most 1 tree late
  if (proofTrees.length + 1 === s.statusAllProofs.length) {
    console.log("CREATING PROOF TREE");
    // we are behind on the number of proof trees, create one
    let pt = new ProofTree(
      s.statusProofName,
      $("#prooftree")[0],
      $(window).width(),
      $("#prooftree").height(),
      function() { $("#loading").css("display", ""); },
      function() { $("#loading").css("display", "none"); }
    );
    proofTrees.unshift(pt);
    return;
  }
  // multiple trees might have been finished at once?
  while (proofTrees.length > s.statusAllProofs.length) {
    proofTrees.shift();
  }
  if (proofTrees.length !== s.statusAllProofs.length) {
    alert("Error: we are missing multiple proof trees!")
  }
}
