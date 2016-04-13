import * as EditStage from "./edit-stage";
import * as Global from "../global-variables";
import { theme } from "../theme";

let CoqMode = ace.require("peacoq-js/mode-coq").Mode;

export function clearEdit(): void {
  Global.tabs.pretty.div.html("");
  _(Global.getAllEditorTabs()).each(t => {
    t.setCaptionSuffix("");
    t.setValue("", false)
  });
}

export function displayEdit(edit: IEdit): void {
  let stage = edit.stage;
  if (stage instanceof EditStage.Ready) {
  let c = stage.context;
    let g = stage.goals;
    Global.tabs.pretty.div.html("");
    _(c).take(1).each((g) => {
      Global.tabs.pretty.div.append(g.getHTML());
    });
    Global.tabs.pretty.click();
    // TODO: if performance becomes an issue, do this more lazily?
    Global.tabs.foreground.setValue(
      _(g.fgGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.foreground.setCaptionSuffix("(" + g.fgGoals.length + ")");
    let bgGoals = _(g.bgGoals).map((ba) => [].concat(ba.before, ba.after)).flatten().value();
    Global.tabs.background.setValue(
      _(bgGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.background.setCaptionSuffix("(" + bgGoals.length + ")");
    Global.tabs.shelved.setValue(
      _(g.shelvedGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.shelved.setCaptionSuffix("(" + g.shelvedGoals.length + ")");
    Global.tabs.givenUp.setValue(
      _(g.givenUpGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.givenUp.setCaptionSuffix("(" + g.givenUpGoals.length + ")");
  }
}

export function setupEditor(e: AceAjax.Editor) {
  e.setTheme(theme.aceTheme);
  //let OCamlMode = ace.require("ace/mode/ocaml").Mode;

  //ace.require("ace/keyboard/textarea");
  e.session.setMode(new CoqMode());
  //e.getSession().setMode("coq");
  e.setOption("tabSize", 2);
  e.setHighlightActiveLine(false);
  e.session.setUseSoftTabs(true);
  e.$blockScrolling = Infinity; // pestering warning
}
