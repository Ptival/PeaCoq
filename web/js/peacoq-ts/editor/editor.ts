import * as Edit from "./edit";
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

export function displayEdit(c: PeaCoqContext): void {
    Global.tabs.pretty.div.html("");
    debugger;
    _(c.fgGoals).take(1).each(g => {
      Global.tabs.pretty.div.append(g.ppgoal.getHTML());
    });
    Global.tabs.pretty.click();
    // TODO: if performance becomes an issue, do this more lazily?
    Global.tabs.foreground.setValue(
      _(c.fgGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.foreground.setCaptionSuffix("(" + c.fgGoals.length + ")");
    let bgGoals = _(c.bgGoals).map((ba) => [].concat(ba.before, ba.after)).flatten().value();
    Global.tabs.background.setValue(
      _(bgGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.background.setCaptionSuffix("(" + bgGoals.length + ")");
    Global.tabs.shelved.setValue(
      _(c.shelvedGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.shelved.setCaptionSuffix("(" + c.shelvedGoals.length + ")");
    Global.tabs.givenUp.setValue(
      _(c.givenUpGoals).map((g) => g.toString()).value().join("\n\n\n"), false
    );
    Global.tabs.givenUp.setCaptionSuffix("(" + c.givenUpGoals.length + ")");
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
