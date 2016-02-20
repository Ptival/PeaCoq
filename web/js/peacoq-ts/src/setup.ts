let coqDocument: CoqDocument = undefined;

$(document).ready(() => {

  resetCoqtop();

  let pstyle = 'border: 1px solid #dfdfdf;';

  $('#interface').w2layout({
    name: 'layout',
    panels: [
      { type: 'top', size: 31, resizable: false, style: pstyle, content: $("<div>", { id: "toolbar" }) },
      { type: 'left', size: "50%", overflow: 'hidden', resizable: true, style: pstyle, content: $("<div>", { id: "editor", style: "height: 100%" }) },
      { type: 'main', size: "50%", style: pstyle, overflow: 'hidden', content: $("<div>", { id: "right" }) },
      { type: 'bottom', size: "50%", overflow: 'hidden', resizable: true, style: pstyle, content: $("<div>", { id: "prooftree" }) },
    ]
  });

  let editor: AceAjax.Editor = ace.edit("editor");
  coqDocument = new CoqDocument(editor);
  setupEditor(editor);
  editor.resize();
  editor.focus();

  $().w2layout({
    name: 'right-layout',
    panels: [
      { type: 'main', size: "50%", resizable: true, style: pstyle, tabs: { tabs: [], } },
      { type: 'bottom', size: "50%", resizable: true, style: pstyle, tabs: { tabs: [], } },
    ],
  });

  w2ui["right-layout"].on({ type: "render", execute: "after" }, () => {
    pretty = new Tab("pretty", "Pretty", "right-layout", "main");
    foreground = new EditorTab("foreground", "Foreground", "right-layout", "main");
    background = new EditorTab("background", "Background", "right-layout", "main");
    shelved = new EditorTab("shelved", "Shelved", "right-layout", "main");
    givenUp = new EditorTab("givenup", "Given up", "right-layout", "main");
    w2ui["right-layout_main_tabs"].click("pretty");

    notices = new EditorTab("notices", "Notices", "right-layout", "bottom");
    warnings = new EditorTab("warnings", "Warnings", "right-layout", "bottom");
    errors = new EditorTab("errors", "Errors", "right-layout", "bottom");
    infos = new EditorTab("infos", "Infos", "right-layout", "bottom");
    jobs = new EditorTab("jobs", "Jobs", "right-layout", "bottom");
    feedback = new EditorTab("feedback", "Feedback", "right-layout", "bottom");
    w2ui["right-layout_bottom_tabs"].click("notices");
  })

  w2ui["layout"].content("main", w2ui["right-layout"]);

  $(window).resize(onResize);
  w2ui['layout'].on({ type: "resize", execute: "after" }, onResize);
  w2ui['right-layout'].on({ type: "resize", execute: "after" }, onResize);

  _(keybindings).each(function(binding) {
    $(document).bind("keydown", binding.jQ, binding.handler);
  });

  setupToolbar();
  setupSyntaxHovering();

  peaCoqAddHandlers.push(proofTreeOnAdd);
  peaCoqGetContextHandlers.push(proofTreeOnGetContext);
  peaCoqEditAtHandlers.push(proofTreeOnEditAt);
  //peaCoqGoalHandlers.push(proofTreeOnGoal);
  peaCoqStatusHandlers.push(proofTreeOnStatus);
});

let lastStatus: Status = undefined;
let lastStateId: number = undefined;

/*
We only react to commands that look like tactics. For now, the
heuristic is that it does not start with an uppercase character.
To take into account the command, we lookup whether this command
was expected (for instance, if the tree mode asked for it).
If it already existed or was expected, nothing is done.
If it was unexpected, let's create an empty, nameless group to hold it.
*/
function proofTreeOnAdd(s: string, r: AddReturn): void {
  lastStateId = r.stateId;

  if (proofTrees.length === 0) { return; }
  let activeProofTree = proofTrees[0];
  let curNode = activeProofTree.curNode;
  let trimmed = coqTrim(s);

  if (isUpperCase(trimmed[0])) {
    assert(curNode instanceof GoalNode, "proofTreeOnAdd: curNode instanceof GoalNode");
    (<GoalNode>curNode).stateIds.push(r.stateId);
    return;
  }

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
  lastStateId = sid;
  let curNode = activeProofTree.curNode;

  // clean up necessary for tactics waiting
  if (activeProofTree.tacticWaitingForContext) {
    let tac = activeProofTree.tacticWaitingForContext;
    _(tac.parentGroup.tactics).remove((t: Tactic) => tac.tactic === t.tactic);
    activeProofTree.tacticWaitingForContext = undefined;
    activeProofTree.update();
  }

  if (curNode instanceof GoalNode) {
    let ancestorGoals = curNode.getGoalAncestors();
    // first, get rid of all stored stateIds > sid
    let allGoals = activeProofTree.rootNode.getAllGoalDescendants();
    _(allGoals).each((g) => {
      g.stateIds = _(g.stateIds).filter((s) => s <= sid).value();
    })
    let target = _(ancestorGoals).find((g) => {
      return _(g.stateIds).some((s) => s === sid);
    });
    if (target) {
      activeProofTree.curNode = target;
      activeProofTree.update();
      if (activeProofTree.tacticWaitingForContext) {
        throw "TODO: proofTreeOnEditAt tactic waiting to be cleared";
      }
    } else {
      proofTrees = [];
      $("#prooftree").empty();
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

  if (lastStatus.statusProofName === null) { return; }

  // we only create GoalNodes if this is the root or if a tactic has been ran
  if (activeProofTree.rootNode === undefined) {
    assert(c.length === 1, "proofTreeOnGetContext: c.length === 1");
    let g = new GoalNode(activeProofTree, undefined, c[0]);
    assert(activeProofTree.rootNode !== undefined, "proofTreeOnGetContext: new GoalNode should set rootNode");
    g.stateIds.push(lastStateId);
    activeProofTree.curNode = g;
    activeProofTree.update();
  }

  if (tacticWaiting) {
    // FIRST clear tacticWaitingForContext
    activeProofTree.tacticWaitingForContext = undefined;
    if (c.length === 0) { // tactic solved the goal!
      curNode.onSolved();
      return;
    } else {
      let gs =
        _(c).map(function(goal) {
          return new GoalNode(activeProofTree, tacticWaiting.parentGroup, goal);
        }).value();
      tacticWaiting.goals = gs;
      let curGoal = gs[0];
      curGoal.stateIds.push(lastStateId);
      activeProofTree.curNode = curGoal;
      activeProofTree.update();
    }
  }
}

function proofTreeOnStatus(s: Status): void {
  lastStatus = s;
  // hopefully we are always at most 1 tree late
  if (proofTrees.length + 1 === s.statusAllProofs.length) {
    // we are behind on the number of proof trees, create one
    let pt = new ProofTree(
      s.statusProofName,
      $("#prooftree")[0],
      $("#prooftree").parent().width(),
      $("#prooftree").parent().height(),
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

function onResize(): void {
  //$("#editor").css("height", parentHeight);
  coqDocument.editor.resize();
  //foreground.onResize();
  //background.onResize();
  let activeProofTree = getActiveProofTree();
  if (activeProofTree) {
    let parent = $("#prooftree").parent();
    activeProofTree.resize(parent.width(), parent.height());
  }
}

function setupToolbar(): void {

  $("<input>", {
    "id": "filepicker",
    "type": "file",
    "style": "display: none;",
  }).appendTo($("body"));

  $("#filepicker").on("change", function() {
    // TODO: warning about resetting Coq/saving file
    loadFile();
    $(this).val(""); // forces change when same file is picked
  });

  $("#toolbar").w2toolbar({
    name: 'w2toolbar',
    items: [
      { type: 'button', id: 'toolbar-load-local', caption: 'Load', img: 'glyphicon glyphicon-floppy-open', onClick: () => loadLocal() },
      { type: 'button', id: 'toolbar-save-local', caption: 'Save', img: 'glyphicon glyphicon-floppy-save' },
      { type: 'break' },
      { type: 'button', id: 'toolbar-previous', caption: 'Previous', img: 'glyphicon glyphicon-arrow-up', onClick: () => onPrevious(coqDocument) },
      { type: 'button', id: 'toolbar-next', caption: 'Next', img: 'glyphicon glyphicon-arrow-down', onClick: () => onNext(coqDocument) },
      { type: 'button', id: 'toolbar-to-caret', caption: 'To Caret', img: 'glyphicon glyphicon-arrow-right', onClick: () => onGotoCaret(coqDocument) },
    ]
  });

}
