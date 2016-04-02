import { theme } from "./theme";

let CoqMode = ace.require("peacoq-js/mode-coq").Mode;

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
