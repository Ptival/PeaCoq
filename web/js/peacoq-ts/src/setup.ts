let coqDocument: CoqDocument = undefined;
let layout: W2UI.W2Layout;
let rightLayout: W2UI.W2Layout;
let contextTabs: W2UI.W2Tabs;
let coqtopTabs: W2UI.W2Tabs;

$(document).ready(() => {

  resetCoqtop();

  let pstyle = '';// 'border: 1px solid #dfdfdf;';

  $('#interface').w2layout({
    name: 'layout',
    panels: [
      { type: 'top', size: 34, resizable: false, style: pstyle, content: $("<div>", { id: "toolbar" }) },
      { type: 'left', size: "50%", overflow: 'hidden', resizable: true, style: pstyle, content: $("<div>", { id: "editor", style: "height: 100%" }) },
      { type: 'main', size: "50%", style: pstyle, overflow: 'hidden', content: $("<div>", { id: "right" }) },
      { type: 'bottom', hidden: true, size: "30%", overflow: 'hidden', resizable: true, style: pstyle, content: $("<div>", { id: "prooftree" }) },
    ]
  });

  let editor: AceAjax.Editor = ace.edit("editor");
  editor.selection.on("changeCursor", (e) => {
    let cursorPosition = editor.selection.getCursor();
    _(coqDocument.editsProcessed).each((e: ProcessedEdit) => {
      if (e.containsPosition(cursorPosition)) {
        updateCoqtopTabs(e.goals, e.context);
        console.log(e.stateId);
      }
    });
  });
  //editor.selection.on("changeSelection", (e) => { console.log(e); });
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

  layout = w2ui["layout"];
  rightLayout = w2ui["right-layout"];
  contextTabs = w2ui["right-layout_main_tabs"];
  contextTabs.onClick = function(event) {
    $('#myTabsContent').html(event.target);
  };
  coqtopTabs = w2ui["right-layout_bottom_tabs"];

  rightLayout.on({ type: "render", execute: "after" }, () => {
    pretty = new Tab("pretty", "Pretty", "right-layout", "main");
    pretty.div.css("padding-left", "4px");
    foreground = new EditorTab("foreground", "Foreground", "right-layout", "main");
    background = new EditorTab("background", "Background", "right-layout", "main");
    shelved = new EditorTab("shelved", "Shelved", "right-layout", "main");
    givenUp = new EditorTab("givenup", "Given up", "right-layout", "main");
    contextTabs.click("pretty");

    notices = new EditorTab("notices", "Notices", "right-layout", "bottom");
    warnings = new EditorTab("warnings", "Warnings", "right-layout", "bottom");
    errors = new EditorTab("errors", "Errors", "right-layout", "bottom");
    infos = new EditorTab("infos", "Infos", "right-layout", "bottom");
    debug = new EditorTab("debug", "Debug", "right-layout", "bottom");
    failures = new EditorTab("failures", "Failures", "right-layout", "bottom");
    jobs = new EditorTab("jobs", "Jobs", "right-layout", "bottom");
    feedback = new EditorTab("feedback", "Feedback", "right-layout", "bottom");
    coqtopTabs.click("notices");
  })

  layout.content("main", rightLayout);

  $(window).resize(onResize);
  layout.on({ type: "resize", execute: "after" }, onResize);
  rightLayout.on({ type: "resize", execute: "after" }, onResize);
  layout.on({ type: "hide", execute: "after" }, () => { coqDocument.recenterEditor(); });
  layout.on({ type: "show", execute: "after" }, () => { coqDocument.recenterEditor(); });

  _(keybindings).each(function(binding) {
    $(document).bind("keydown", binding.jQ, binding.handler);
  });

  setupToolbar();
  setupSyntaxHovering();
  Theme.setupTheme();

  // peaCoqAddHandlers.push(proofTreeOnAdd);
  // peaCoqGetContextHandlers.push(proofTreeOnGetContext);
  peaCoqEditAtHandlers.push(proofTreeOnEditAt);
  peaCoqEditAtHandlers.push(editorOnEditAt);
  // peaCoqGoalHandlers.push(proofTreeOnGoal);
  peaCoqStatusHandlers.push(proofTreeOnStatus);
  editHandlers.push(proofTreeOnEdit);
});

let lastStatus: Status;

function editorOnEditAt(sid: number) {
  let edit = _(coqDocument.editsProcessed).find((e) => e.stateId === sid);
  if (edit) {
    updateCoqtopTabs(edit.goals, edit.context);
  }
}

function proofTreeOnStatus(s) {
  lastStatus = s;
}

function updateCoqtopTabs(goals: Goals, context: PeaCoqContext) {
  clearCoqtopTabs();
  if (context.length > 0) {
    pretty.div.append(context[0].getHTML());
    foreground.setValue(goals.fgGoals[0].toString(), false);
  }
}

function proofTreeOnEdit(
  query: string,
  stateId: number,
  lastStatus: Status,
  status: Status,
  goals: Goals,
  context: PeaCoqContext
): void {

  let trimmed = coqTrim(query);

  updateCoqtopTabs(goals, context);

  if (
    lastStatus.statusAllProofs.length + 1 === status.statusAllProofs.length
    &&
    proofTrees.length + 1 === status.statusAllProofs.length
  ) {
    // we are behind on the number of proof trees, create one
    showProofTreePanel()
      .then(() => { // needs to be before for width/height
        let pt = new ProofTree(
          status.statusProofName,
          $("#prooftree")[0],
          $("#prooftree").parent().width(),
          $("#prooftree").parent().height()
        );
        proofTrees.unshift(pt);
        assert(context.length === 1, "proofTreeOnGetContext: c.length === 1, c.length: " + context.length);
        let g = new GoalNode(pt, nothing(), goals, context[0]);
        assert(pt.rootNode !== undefined, "proofTreeOnGetContext: new GoalNode should set rootNode");
        g.stateIds.push(stateId);
        pt.curNode = g;
        pt.update();
      });
    return;
  } else {
    // multiple trees might have been finished at once?
    while (proofTrees.length > status.statusAllProofs.length) {
      proofTrees.shift();
      if (proofTrees.length === 0) {
        $("#prooftree").empty();
        hideProofTreePanel();
      }
    }
  }

  if (proofTrees.length === 0) { return; }

  let activeProofTree = proofTrees[0];
  let curNode = activeProofTree.curNode;

  if (isUpperCase(trimmed[0]) || _(bullets).includes(trimmed)) {
    curNode.goals = goals;
    curNode.stateIds.push(stateId);
    return;
  }

  let tactic: Tactic = _.find(curNode.getTactics(), (t) => t.tactic === trimmed);

  let tacticGroup: TacticGroupNode = (
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
  let goalsBefore = curNode.goals;
  let goalsAfter = goals;
  let nbRelevantGoals =
    goalsBefore.bgGoals.length === goalsAfter.bgGoals.length
      ? goalsAfter.fgGoals.length - (goalsBefore.fgGoals.length - 1)
      : 0;
  let relevantGoals = context.slice(0, nbRelevantGoals);

  let goalNodes: GoalNode[] =
    _(relevantGoals).map(function(goal) {
      return new GoalNode(
        activeProofTree,
        just(tacticGroup),
        goals,
        goal
      );
    }).value();

  if (!tactic) {
    curNode.tacticGroups.push(tacticGroup);
    tactic = new Tactic(trimmed, tacticGroup, goalNodes);
    tacticGroup.tactics.push(tactic);
  } else {
    tactic.goals = goalNodes;
  }

  tacticGroup.isProcessed = true;

  if (goalNodes.length > 0) {
    let curGoal: GoalNode = goalNodes[0];
    curGoal.stateIds.push(stateId);
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
function proofTreeOnEditAt(sid: number): void {

  if (proofTrees.length === 0) { return; }
  let activeProofTree = proofTrees[0];
  //lastStateId = sid;
  let curNode = activeProofTree.curNode;

  // clean up necessary for tactics waiting
  activeProofTree.tacticWaiting = nothing();

  // first, get rid of all stored stateIds > sid
  // and mark their children tactic groups unprocessed
  let allGoals = activeProofTree.rootNode.getAllGoalDescendants();
  _(allGoals).each((g) => {
    if (_(g.stateIds).some((s) => s >= sid)) {
      _(g.tacticGroups).each((g) => { g.isProcessed = false; });
    }
    g.stateIds = _(g.stateIds).filter((s) => s <= sid).value();
  });
  let target = _(allGoals).find((g) => {
    return _(g.stateIds).some((s) => s === sid);
  });
  if (target) {
    activeProofTree.curNode = target;
    activeProofTree.update();
  } else {
    proofTrees = [];
    hideProofTreePanel();
    $("#prooftree").empty();
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

  $("<a>", {
    "download": "output.v",
    "id": "save-local-link",
  })
    .css("display", "none")
    .appendTo($("body"))
    ;

  $("#toolbar").w2toolbar({
    name: 'w2toolbar',
    items: [
      { type: 'button', id: 'toolbar-load-local', caption: 'Load', img: 'glyphicon glyphicon-floppy-open', onClick: () => loadLocal() },
      { type: 'button', id: 'toolbar-save-local', caption: 'Save', img: 'glyphicon glyphicon-floppy-save', onClick: () => saveLocal() },
      { type: 'break' },
      { type: 'button', id: 'toolbar-previous', caption: 'Previous', img: 'glyphicon glyphicon-arrow-up', onClick: () => onPrevious(coqDocument) },
      { type: 'button', id: 'toolbar-next', caption: 'Next', img: 'glyphicon glyphicon-arrow-down', onClick: () => onNext(coqDocument) },
      { type: 'button', id: 'toolbar-to-caret', caption: 'To Caret', img: 'glyphicon glyphicon-arrow-right', onClick: () => onGotoCaret(coqDocument) },
      { type: 'spacer' },
      { type: 'radio', id: 'bright', group: '1', caption: 'Bright', checked: true, onClick: Theme.switchToBright },
      { type: 'radio', id: 'dark', group: '1', caption: 'Dark', onClick: Theme.switchToDark },
    ]
  });

}

function hideProofTreePanel(): void {
  layout.hide("bottom");
}

function showProofTreePanel(): Promise<{}> {
  return new Promise(function(onFulfilled) {
    let handler = function(event) {
      event.onComplete = onFulfilled;
      layout.off("show", handler);
    };
    layout.on("show", handler);
    layout.show("bottom");
  });
}
