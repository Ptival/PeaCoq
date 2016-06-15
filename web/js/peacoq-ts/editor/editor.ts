import * as Edit from "./edit";
import * as Global from "../global-variables";
import { theme } from "../theme";

const CoqMode = ace.require("peacoq-js/mode-coq").Mode;

class Editor implements IEditor {
  constructor(
    public document: ICoqDocument
  ) { }
}

export function setupEditor(e: AceAjax.Editor) {
  e.setTheme(theme.aceTheme);
  //const OCamlMode = ace.require("ace/mode/ocaml").Mode;

  //ace.require("ace/keyboard/textarea");
  e.session.setMode(new CoqMode());
  //e.getSession().setMode("coq");
  e.setOption("tabSize", 2);
  e.setHighlightActiveLine(false);
  e.session.setUseSoftTabs(true);
  e.$blockScrolling = Infinity; // pestering warning
}
